import Hypernets.Copying.CopyingNestedRows

/-! A three-branch frame with one complete three-input resource row per
output. The explicit input bijection fixes the external order of every branch. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Hypernets.Copying.CopyingMerge.Frame
open Graph
variable (arity : Fin 3 → Nat) (N k h : Nat)
    (inputs : Bijection (Σ b : Fin 3, Fin (arity b)) (Fin N))
abbrev Resource := Fin (environmentInterface k h).length
abbrev Internal := Fin 3 × Resource k h
abbrev Edge := Fin 3 ⊕ Resource k h
abbrev Vertex := Port (Internal k h) (List.replicate N Wire.term).length (environmentInterface k h).length

def branchInput (b : Fin 3) (i : Fin (arity b)) : Vertex N k h :=
  .input ⟨(inputs.toFun ⟨b,i⟩).val,by have := (inputs.toFun ⟨b,i⟩).isLt; simpa⟩
def branchOutput (b : Fin 3) (i : Resource k h) : Vertex N k h := .internal (b,i)
def rowInput (i : Resource k h) (b : Fin 3) : Vertex N k h := branchOutput N k h b i

def hole : Edge k h → Hole
  | .inl b => ⟨b.val,List.replicate (arity b) .term,environmentInterface k h⟩
  | .inr i => ⟨3+i.val,List.replicate 3 (environmentInterface k h)[i],[(environmentInterface k h)[i]]⟩
def source : Edge k h → List (Vertex N k h)
  | .inl b => (List.finRange (arity b)).map (branchInput arity N k h inputs b)
  | .inr i => (List.finRange 3).map (rowInput N k h i)
def target : Edge k h → List (Vertex N k h)
  | .inl b => (List.finRange _).map (branchOutput N k h b)
  | .inr i => [.output i]
def internalLabel (i : Internal k h) : Wire := (environmentInterface k h)[i.2]

theorem branchInput_injective : Function.Injective (fun x : Σ b : Fin 3, Fin (arity b) =>
    branchInput arity N k h inputs x.1 x.2) := by
  intro x y eq
  apply inputs.injective
  have value := congrArg (fun v : Vertex N k h => match v with | .input i => i.val | _ => 0) eq
  exact Fin.ext value

theorem branchOutput_injective (b : Fin 3) : Function.Injective (branchOutput N k h b) := by
  intro i j eq
  exact congrArg Prod.snd (Port.internal.inj eq)
theorem rowInput_injective (i : Resource k h) : Function.Injective (rowInput N k h i) := by
  intro b c eq
  exact congrArg Prod.fst (Port.internal.inj eq)

@[simp] theorem mem_input (b : Fin 3) (v : Vertex N k h) :
    v ∈ (List.finRange (arity b)).map (branchInput arity N k h inputs b) ↔
      ∃ i, v = branchInput arity N k h inputs b i := by simp [eq_comm]
@[simp] theorem mem_output (b : Fin 3) (v : Vertex N k h) :
    v ∈ (List.finRange _).map (branchOutput N k h b) ↔ ∃ i, v = branchOutput N k h b i := by simp [eq_comm]
@[simp] theorem mem_row (i : Resource k h) (v : Vertex N k h) :
    v ∈ (List.finRange 3).map (rowInput N k h i) ↔ ∃ b, v = rowInput N k h i b := by simp [eq_comm]

def net : Net primitiveSignature (List.replicate N Wire.term) (environmentInterface k h) where
  Internal := Internal k h
  Edge := Edge k h
  finiteInternal := ⟨(List.finRange 3).flatMap (fun b =>
    (List.finRange (environmentInterface k h).length).map (fun i => (b,i))),by
      intro ⟨b,i⟩
      exact List.mem_flatMap.mpr ⟨b,List.mem_finRange b,List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩⟩⟩
  finiteEdge := .sum (Enumeration.fin 3) (Enumeration.fin _)
  internalLabel := internalLabel k h
  edgeLabel e := .hole (hole arity k h e)
  source := source arity N k h inputs
  target := target N k h
  source_nodup e := by
    rcases e with b | i
    · apply nodup_map_on (finRange_nodup _)
      intro x _ y _ eq
      exact eq_of_heq (Sigma.mk.inj (branchInput_injective arity N k h inputs eq)).2
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => rowInput_injective N k h i eq)
  target_nodup e := by
    rcases e with b | i
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => branchOutput_injective N k h b eq)
    · simp [target]
  source_unique := by
    intro v a b ha hb
    rcases a with a | a
    all_goals rcases b with b | b
    · obtain ⟨i,eq⟩ := (mem_input arity N k h inputs a v).mp ha
      obtain ⟨j,eq'⟩ := (mem_input arity N k h inputs b v).mp hb
      have same : (⟨a,i⟩ : Σ tag : Fin 3, Fin (arity tag)) = ⟨b,j⟩ :=
        branchInput_injective arity N k h inputs (eq.symm.trans eq')
      exact congrArg Sum.inl (congrArg Sigma.fst same)
    · obtain ⟨i,rfl⟩ := (mem_input arity N k h inputs a v).mp ha
      obtain ⟨j,eq⟩ := (mem_row N k h b _).mp hb
      cases eq
    · obtain ⟨i,rfl⟩ := (mem_input arity N k h inputs b v).mp hb
      obtain ⟨j,eq⟩ := (mem_row N k h a _).mp ha
      cases eq
    · obtain ⟨i,eq⟩ := (mem_row N k h a v).mp ha
      obtain ⟨j,eq'⟩ := (mem_row N k h b v).mp hb
      exact congrArg Sum.inr (congrArg Prod.snd (Port.internal.inj (eq.symm.trans eq')))
  target_unique := by
    intro v a b ha hb
    rcases a with a | a
    all_goals rcases b with b | b
    · obtain ⟨i,eq⟩ := (mem_output N k h a v).mp ha
      obtain ⟨j,eq'⟩ := (mem_output N k h b v).mp hb
      exact congrArg Sum.inl (congrArg Prod.fst (Port.internal.inj (eq.symm.trans eq')))
    · obtain ⟨i,rfl⟩ := (mem_output N k h a v).mp ha
      cases List.mem_singleton.mp hb
    · obtain ⟨i,rfl⟩ := (mem_output N k h b v).mp hb
      cases List.mem_singleton.mp ha
    · exact congrArg Sum.inr (Port.output.inj ((List.mem_singleton.mp ha).symm.trans (List.mem_singleton.mp hb)))
  source_coverage v := by
    cases v with
    | internal v => exact ⟨fun _ => by simp [Port.IsOutput],fun _ =>
        ⟨.inr v.2,(mem_row N k h v.2 _).mpr ⟨v.1,rfl⟩⟩⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let x := inputs.invFun ⟨i.val,by simpa using i.isLt⟩
      refine ⟨.inl x.1,(mem_input arity N k h inputs x.1 _).mpr ⟨x.2,?_⟩⟩
      apply congrArg Port.input
      apply Fin.ext
      exact (congrArg Fin.val (inputs.right_inv ⟨i.val,by simpa using i.isLt⟩)).symm
    | output i =>
      constructor
      · rintro ⟨e,he⟩
        rcases e with b | r
        · obtain ⟨j,eq⟩ := (mem_input arity N k h inputs b _).mp he; cases eq
        · obtain ⟨j,eq⟩ := (mem_row N k h r _).mp he; cases eq
      · exact fun no => False.elim (no trivial)
  target_coverage v := by
    cases v with
    | internal v => exact ⟨fun _ => by simp [Port.IsInput],fun _ =>
        ⟨.inl v.1,(mem_output N k h v.1 _).mpr ⟨v.2,rfl⟩⟩⟩
    | output i => exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨.inr i,List.mem_cons_self⟩⟩
    | input i =>
      constructor
      · rintro ⟨e,he⟩
        rcases e with b | r
        · obtain ⟨j,eq⟩ := (mem_output N k h b _).mp he; cases eq
        · cases List.mem_singleton.mp he
      · exact fun no => False.elim (no trivial)
  source_typed e := by
    rcases e with b | i
    · simp [source,hole,branchInput,Port.label,primitiveSignature,List.map_map,
        Function.comp_def,List.map_const',List.length_finRange,List.getElem_replicate]
    · simp [source,hole,rowInput,branchOutput,Port.label,internalLabel,primitiveSignature,List.map_map,
        Function.comp_def,List.map_const',List.length_finRange,List.finRange]
  target_typed e := by
    rcases e with b | i
    · simp [target,hole,branchOutput,Port.label,internalLabel,primitiveSignature,
        Function.comp_def,List.finRange,List.map_ofFn,List.ofFn_getElem]
    · rfl

def graph (d : Nat) : Hypernet d (List.replicate N .term) (environmentInterface k h) :=
  (net arity N k h inputs).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)
end Hypernets.Copying.CopyingMerge.Frame
