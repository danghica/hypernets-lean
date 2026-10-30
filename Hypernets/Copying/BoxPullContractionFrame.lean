import Hypernets.Copying.ApplicationFrame

/-! Attach one actual contraction to two adjacent output wires, retaining
every other ordered boundary wire directly. There are no identity edges. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

def prefixPort (I A B : List Wire) (s : ShareSort) (i : Fin A.length) :
    Port (Fin 2) I.length (A ++ s.wire :: B).length := .output ⟨i.val,by simp; omega⟩

def suffixPort (I A B : List Wire) (s : ShareSort) (i : Fin B.length) :
    Port (Fin 2) I.length (A ++ s.wire :: B).length := .output ⟨A.length+1+i.val,by simp; omega⟩

def selectedPort (I A B : List Wire) (s : ShareSort) :
    Port (Fin 2) I.length (A ++ s.wire :: B).length := .output ⟨A.length,by simp⟩

def prefixPorts (I A B : List Wire) (s : ShareSort) :=
  (List.finRange A.length).map (prefixPort I A B s)

def suffixPorts (I A B : List Wire) (s : ShareSort) :=
  (List.finRange B.length).map (suffixPort I A B s)

@[simp] theorem mem_prefixPorts (I A B : List Wire) (s : ShareSort) (v) :
    v ∈ prefixPorts I A B s ↔ ∃ i, v = prefixPort I A B s i := by
  simp [prefixPorts,eq_comm]

@[simp] theorem mem_suffixPorts (I A B : List Wire) (s : ShareSort) (v) :
    v ∈ suffixPorts I A B s ↔ ∃ i, v = suffixPort I A B s i := by
  simp [suffixPorts,eq_comm]

theorem prefix_suffix_ne (I A B : List Wire) (s : ShareSort) (i j) :
    prefixPort I A B s i ≠ suffixPort I A B s j := by
  intro eq
  have e := congrArg Fin.val (Port.output.inj eq)
  have bound := i.isLt
  dsimp [prefixPort,suffixPort] at e
  omega

theorem prefix_selected_ne (I A B : List Wire) (s : ShareSort) (i) :
    prefixPort I A B s i ≠ selectedPort I A B s := by
  intro eq
  have e := congrArg Fin.val (Port.output.inj eq)
  have bound := i.isLt
  dsimp [prefixPort,selectedPort] at e
  omega

theorem suffix_selected_ne (I A B : List Wire) (s : ShareSort) (i) :
    suffixPort I A B s i ≠ selectedPort I A B s := by
  intro eq
  have e := congrArg Fin.val (Port.output.inj eq)
  dsimp [suffixPort,selectedPort] at e
  omega

theorem prefixPorts_nodup (I A B : List Wire) (s : ShareSort) :
    (prefixPorts I A B s).Nodup := by
  apply nodup_map_on (finRange_nodup _)
  intro i j _ _ eq
  have h := congrArg Fin.val (Port.output.inj eq)
  exact Fin.ext h

theorem suffixPorts_nodup (I A B : List Wire) (s : ShareSort) :
    (suffixPorts I A B s).Nodup := by
  apply nodup_map_on (finRange_nodup _)
  intro i j _ _ eq
  have e := congrArg Fin.val (Port.output.inj eq)
  apply Fin.ext
  dsimp [suffixPort] at e
  omega

def frameLabel (I A B : List Wire) (s : ShareSort) : Bool → Primitive
  | false => .hole ⟨0,I,A ++ s.wire :: s.wire :: B⟩
  | true => .contraction s

def frameSource (I A B : List Wire) (s : ShareSort) :
    Bool → List (Port (Fin 2) I.length (A ++ s.wire :: B).length)
  | false => (List.finRange I.length).map Port.input
  | true => [.internal 0,.internal 1]

def frameTarget (I A B : List Wire) (s : ShareSort) :
    Bool → List (Port (Fin 2) I.length (A ++ s.wire :: B).length)
  | false => prefixPorts I A B s ++ .internal 0 :: .internal 1 :: suffixPorts I A B s
  | true => [selectedPort I A B s]

/-- The exact two-edge frame: one original graph hole and one contraction,
with its two distinct incident vertices freshly internalized. -/
def frame (I A B : List Wire) (s : ShareSort) :
    Net primitiveSignature I (A ++ s.wire :: B) where
  Internal := Fin 2
  Edge := Bool
  finiteInternal := Enumeration.fin 2
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := s.wire
  edgeLabel := frameLabel I A B s
  source := frameSource I A B s
  target := frameTarget I A B s
  source_nodup b := by
    cases b
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => Port.input.inj eq)
    · simp [frameSource]
  target_nodup b := by
    cases b
    · apply List.nodup_append.mpr
      refine ⟨prefixPorts_nodup _ _ _ _,?_,?_⟩
      · simp [suffixPorts_nodup,suffixPort]
      · intro a ha b hb eq
        obtain ⟨i,rfl⟩ := (mem_prefixPorts _ _ _ _ _).mp ha
        rcases List.mem_cons.mp hb with rfl | hb
        · cases eq
        rcases List.mem_cons.mp hb with rfl | hb
        · cases eq
        obtain ⟨j,rfl⟩ := (mem_suffixPorts _ _ _ _ _).mp hb
        exact prefix_suffix_ne _ _ _ _ _ _ eq
    · simp [frameTarget]
  source_unique := by
    intro v b c hb hc
    cases v <;> cases b <;> cases c <;> simp_all [frameSource]
  target_unique := by
    intro v b c hb hc
    have disjoint : ∀ v, v ∈ frameTarget I A B s false →
        v ≠ selectedPort I A B s := by
      intro v mem
      rcases List.mem_append.mp mem with initial | rest
      · obtain ⟨i,rfl⟩ := (mem_prefixPorts _ _ _ _ _).mp initial
        exact prefix_selected_ne _ _ _ _ _
      · rcases List.mem_cons.mp rest with rfl | rest
        · intro eq; cases eq
        rcases List.mem_cons.mp rest with rfl | rest
        · intro eq; cases eq
        obtain ⟨j,rfl⟩ := (mem_suffixPorts _ _ _ _ _).mp rest
        exact suffix_selected_ne _ _ _ _ _
    cases b <;> cases c
    · rfl
    · exact False.elim (disjoint v hb (List.mem_singleton.mp hc))
    · exact False.elim (disjoint v hc (List.mem_singleton.mp hb))
    · rfl
  source_coverage := by
    intro v
    cases v with
    | internal i =>
      have cases : i = 0 ∨ i = 1 := by omega
      rcases cases with rfl | rfl <;> simp [frameSource,Port.IsOutput]
    | input i => simp [frameSource,Port.IsOutput]
    | output i => simp [frameSource,Port.IsOutput]
  target_coverage := by
    intro v
    cases v with
    | internal i =>
      have cases : i = 0 ∨ i = 1 := by omega
      rcases cases with rfl | rfl <;> simp [frameTarget,prefixPort,suffixPort,selectedPort,Port.IsInput]
    | input i => simp [frameTarget,prefixPort,suffixPort,selectedPort,Port.IsInput]
    | output i =>
      constructor
      · intro _; simp [Port.IsInput]
      · intro _
        by_cases before : i.val < A.length
        · exact ⟨false,List.mem_append_left _ ((mem_prefixPorts _ _ _ _ _).mpr ⟨⟨i.val,before⟩,rfl⟩)⟩
        by_cases middle : i.val = A.length
        · exact ⟨true,List.mem_singleton.mpr (congrArg Port.output (Fin.ext middle))⟩
        · refine ⟨false,List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            ((mem_suffixPorts _ _ _ _ _).mpr ⟨⟨i.val-(A.length+1),?_⟩,?_⟩)))⟩
          · have bound := i.isLt
            simp at bound
            omega
          · apply congrArg Port.output
            apply Fin.ext
            dsimp [suffixPort]
            omega
  source_typed b := by
    cases b
    · simp [frameSource,frameLabel,primitiveSignature,Port.label,Function.comp_def,
        List.finRange,List.map_ofFn,List.ofFn_getElem]
    · rfl
  target_typed b := by
    have initial : (prefixPorts I A B s).map (Port.label (fun _ : Fin 2 => s.wire)) = A := by
      simp [prefixPorts,prefixPort,Port.label,Function.comp_def,List.getElem_append_left,
        List.finRange,List.map_ofFn,List.ofFn_getElem]
    have suffix : (suffixPorts I A B s).map (Port.label (fun _ : Fin 2 => s.wire)) = B := by
      simp [suffixPorts,suffixPort,Port.label,Function.comp_def,List.getElem_append_right,
        List.finRange,List.map_ofFn,Nat.add_assoc]
      simp only [Nat.add_comm 1,List.getElem_cons_succ,List.ofFn_getElem]
    cases b
    · change (prefixPorts I A B s ++ .internal 0 :: .internal 1 :: suffixPorts I A B s).map _ = _
      simp only [List.map_append,List.map_cons,initial,suffix]
      rfl
    · simp [frameTarget,selectedPort,Port.label,frameLabel,primitiveSignature]

def pattern (d : Nat) (I A B : List Wire) (s : ShareSort) : Hypernet d I (A ++ s.wire :: B) :=
  (frame I A B s).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

def filling {d I A B} (s : ShareSort) (G : Hypernet d I (A ++ s.wire :: s.wire :: B))
    (b : Bool) : Hypernet d ((alphabet d).signature.input ((pattern d I A B s).edgeLabel b))
      ((alphabet d).signature.output ((pattern d I A B s).edgeLabel b)) := by
  cases d <;> cases b
  all_goals first | exact G | exact primitiveNet _ (.contraction s)

/-- The original graph with exactly the displayed contraction added to its
two adjacent outputs. All other vertices, edges and ports remain present. -/
def merge {d I A B} (s : ShareSort) (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) :
    Hypernet d I (A ++ s.wire :: B) := (pattern d I A B s).expand (filling s G)

end Hypernets.Copying.BoxPullContraction
