import Hypernets.Copying.AtomEqualityExamples

/-! The micro-beta reduct: connect just the bound output to the stable argument.
Free body outputs and argument outputs retain separate ordered boundary blocks. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph

def spliceHole (F O : List Wire) : Bool → Hole
  | false => ⟨0,[.term],.term :: F⟩
  | true => ⟨1,[.term],O⟩
def freePort (F O : List Wire) {V : Type} (i : Fin F.length) : Port V 1 (F ++ O).length :=
  .output ⟨i.val,by simp; omega⟩
def valuePort (F O : List Wire) {V : Type} (i : Fin O.length) : Port V 1 (F ++ O).length :=
  .output ⟨F.length+i.val,by simp⟩
def freePorts (F O : List Wire) {V : Type} : List (Port V 1 (F ++ O).length) :=
  (List.finRange F.length).map (freePort F O)
def valuePorts (F O : List Wire) {V : Type} : List (Port V 1 (F ++ O).length) :=
  (List.finRange O.length).map (valuePort F O)
@[simp] theorem mem_freePorts (F O : List Wire) {V : Type} (v : Port V 1 (F ++ O).length) :
    v ∈ freePorts F O ↔ ∃ i, v = freePort F O i := by simp [freePorts,eq_comm]
@[simp] theorem mem_valuePorts (F O : List Wire) {V : Type} (v : Port V 1 (F ++ O).length) :
    v ∈ valuePorts F O ↔ ∃ i, v = valuePort F O i := by simp [valuePorts,eq_comm]
theorem freePorts_nodup (F O : List Wire) {V : Type} : (freePorts F O (V := V)).Nodup := by
  apply nodup_map_on (finRange_nodup _)
  intro i j _ _ eq
  have h := congrArg Fin.val (Port.output.inj eq)
  exact Fin.ext h
theorem valuePorts_nodup (F O : List Wire) {V : Type} : (valuePorts F O (V := V)).Nodup := by
  apply nodup_map_on (finRange_nodup _)
  intro i j _ _ eq
  have h := congrArg Fin.val (Port.output.inj eq)
  apply Fin.ext; dsimp [valuePort] at h; omega

def spliceSource (F O : List Wire) : Bool → List (Port (Fin 1) 1 (F ++ O).length)
  | false => [.input 0]
  | true => [.internal 0]
def spliceTarget (F O : List Wire) : Bool → List (Port (Fin 1) 1 (F ++ O).length)
  | false => .internal 0 :: freePorts F O
  | true => valuePorts F O

/-- The only new internal vertex connects bound output zero to the argument input. -/
def spliceFrame (F O : List Wire) : Net primitiveSignature [.term] (F ++ O) where
  Internal := Fin 1
  Edge := Bool
  finiteInternal := Enumeration.fin 1
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := .term
  edgeLabel b := .hole (spliceHole F O b)
  source := spliceSource F O
  target := spliceTarget F O
  source_nodup b := by cases b <;> simp [spliceSource]
  target_nodup b := by cases b <;> simp [spliceTarget,freePorts_nodup,valuePorts_nodup,freePort]
  source_unique := by intro v b c hb hc; cases b <;> cases c <;> simp_all [spliceSource]
  target_unique := by
    intro v b c hb hc
    cases b <;> cases c
    · rfl
    · change v ∈ .internal 0 :: freePorts F O at hb
      rw [List.mem_cons] at hb
      rcases hb with eq | hb
      · subst v; simp [spliceTarget,valuePort] at hc
      · obtain ⟨i,hi⟩ := (mem_freePorts _ _ _).mp hb
        obtain ⟨j,hj⟩ := (mem_valuePorts _ _ _).mp hc
        have eq := congrArg Fin.val (Port.output.inj (hi.symm.trans hj))
        dsimp [freePort,valuePort] at eq
        have := i.isLt; omega
    · change v ∈ .internal 0 :: freePorts F O at hc
      rw [List.mem_cons] at hc
      rcases hc with eq | hc
      · subst v; simp [spliceTarget,valuePort] at hb
      · obtain ⟨i,hi⟩ := (mem_freePorts _ _ _).mp hc
        obtain ⟨j,hj⟩ := (mem_valuePorts _ _ _).mp hb
        have eq := congrArg Fin.val (Port.output.inj (hi.symm.trans hj))
        dsimp [freePort,valuePort] at eq
        have := i.isLt; omega
    · rfl
  source_coverage := by
    intro v; cases v with
    | internal i => have hi : i = 0 := by omega
                    subst i; simp [Port.IsOutput,spliceSource]
    | input i => have hi : i = (0 : Fin 1) := by apply Fin.ext; have := i.isLt; change i.val < 1 at this; change i.val = 0; omega
                 subst i; simp [Port.IsOutput,spliceSource]
    | output i => simp [Port.IsOutput,spliceSource]
  target_coverage := by
    intro v; cases v with
    | internal i => have hi : i = 0 := by omega
                    subst i; simp [Port.IsInput,spliceTarget,freePort,valuePort]
    | input i => simp [Port.IsInput,spliceTarget,freePort,valuePort]
    | output i =>
      constructor
      · intro _; simp [Port.IsInput]
      · intro _
        by_cases h : i.val < F.length
        · exact ⟨false, List.mem_cons_of_mem _ ((mem_freePorts _ _ _).mpr ⟨⟨i.val,h⟩,rfl⟩)⟩
        · refine ⟨true,(mem_valuePorts _ _ _).mpr ⟨⟨i.val-F.length,by have := i.isLt; simp at this; omega⟩,?_⟩⟩
          apply congrArg Port.output; apply Fin.ext; dsimp [valuePort]; omega
  source_typed b := by cases b <;> simp [spliceSource,spliceHole,primitiveSignature,Port.label]
  target_typed b := by
    cases b <;> simp only [spliceTarget,spliceHole,primitiveSignature]
    · change .term :: (freePorts F O).map _ = .term :: F
      congr 1
      simp [freePorts,freePort,Port.label,Function.comp_def,List.getElem_append_left,List.finRange,List.map_ofFn,List.ofFn_getElem]
    · change (valuePorts F O).map _ = O
      simp [valuePorts,valuePort,Port.label,Function.comp_def,List.getElem_append_right,List.finRange,List.map_ofFn,List.ofFn_getElem]

/-- Simultaneous filling removes both temporary holes; no identity wire is inserted. -/
def spliceFill {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    (b : Bool) : Hypernet d
      (primitiveSignature.input (.hole (spliceHole F O b)))
      (primitiveSignature.output (.hole (spliceHole F O b))) := by
  cases b
  · exact B
  · exact G

def splicePattern (d : Nat) (F O : List Wire) : Hypernet d [.term] (F ++ O) :=
  (spliceFrame F O).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)
def spliceFilling {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    (b : Bool) : Hypernet d
      ((alphabet d).signature.input ((splicePattern d F O).edgeLabel b))
      ((alphabet d).signature.output ((splicePattern d F O).edgeLabel b)) := by
  cases d <;> exact spliceFill B G b

def splice {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    Hypernet d [.term] (F ++ O) := (splicePattern d F O).expand (spliceFilling B G)
end Hypernets.Copying.Application
