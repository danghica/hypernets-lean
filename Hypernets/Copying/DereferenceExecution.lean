import Hypernets.Copying.DereferenceResolution

/-! Exact execution of the general local read interaction, stopping at the
copy request required by Figure 19(b), not returning the value prematurely. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

def argument {h} (T : ContractionTree .atom (h+1)) (d : Nat) : (before T d).Vertex := .internal (.inl (0 : Fin 3))

theorem search_argument {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Search.Step (before T d) (.search,inputPort h 0) (.search,argument T d) := by
  apply Search.Step.search (G := before T d) ⟨.reader,(0 : Fin 1)⟩ (.operation (.unary .deref)) _ _ rfl
  · change inputPort h 0 ∈ [inputPort h 0]; exact List.mem_cons_self
  · rfl

theorem instance_returns {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Search.Step (before T d) (.search,argument T d) (.backtrack,argument T d) := by
  apply Search.instance_return (G := before T d) (beforeInstance T d) _ rfl
  change argument T d ∈ [argument T d]; exact List.mem_cons_self

theorem ready {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Search.Step (before T d) (.backtrack,argument T d) (.rewrite,inputPort h 0) :=
  Search.Step.backtrack (G := before T d) ⟨.reader,(0 : Fin 1)⟩ (.unary .deref) (inputPort h 0) _ 0 _ rfl rfl (by decide) rfl rfl

/-- Graph-changing states at the complete local read interface. -/
abbrev State (d h : Nat) := Σ G : Hypernet d (inputs h) [.term], Search.Position G

/-- An honest search/read subsystem; copying and other compute rules remain separate. -/
inductive Step {d h} : State d h → State d h → Prop where
  | search (G : Hypernet d (inputs h) [.term]) {s t} (a : Search.Step G s t) : Step ⟨G,s⟩ ⟨G,t⟩
  | read (T : ContractionTree .atom (h+1)) :
      Step ⟨before T d,(.rewrite,inputPort h 0)⟩ ⟨after T d,(.search,inputPort h 0)⟩

theorem final_normal {d h} {s : State d h} (done : Search.Completed s.2) : ∀ t, ¬ Step s t := by
  intro t step
  cases step with
  | @search G s t step =>
    rcases s with ⟨m,v⟩
    rcases done with ⟨mode,input⟩
    change m = .backtrack at mode
    subst m
    exact Search.final_no_step input step
  | read => cases done.1

def machine (d h : Nat) : Machine (State d h) where
  step := Step
  final s := Search.Completed s.2
  final_normal h := final_normal h _

/-- Three search steps, one dereference computation, then a genuine copy request. -/
theorem read_run {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (machine d h).Steps 5 ⟨before T d,(.search,inputPort h 0)⟩
      ⟨after T d,(.rewrite,inputPort h 0)⟩ :=
  .cons (.search _ (search_argument T d)) (.cons (.search _ (instance_returns T d))
    (.cons (.search _ (ready T d)) (.cons (.read T)
      (.cons (.search _ (requests_copy T d)) (.zero _)))))

/-- The read trace has not returned a value; its pending copy must not be erased. -/
theorem read_pending_copy {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    ¬ (machine d h).final ⟨after T d,(.rewrite,inputPort h 0)⟩ := by
  intro h; cases h.1

/-- Reading consumes the old instance by attaching the required term weakening. -/
theorem instance_discarded {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (after T d).source (afterInstance T d) = (after T d).target ⟨.discard,(0 : Fin 1)⟩ := rfl

/-- Store and result meet at the same new term contraction, in their prescribed order. -/
theorem shared_store_result {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (after T d).source ⟨.share,(2 : Fin 3)⟩ = (after T d).target (afterStore T d) ++ [inputPort h 0] := rfl

/-- The original atom tree is unchanged even when other references remain at its boundary. -/
theorem before_other_input {h} (T : ContractionTree .atom (h+1)) (d : Nat) (i : Fin h) :
    beforeTreeVertex T d (.input ⟨i.val+1,by simpa using i.succ.isLt⟩) = inputPort h i.succ := by
  change Port.map Sum.inl ((beforeFrame h).sourcePort .tree _) = _
  simp [Net.sourcePort,beforeFrame,beforeSource,otherInputs,inputPort,Port.map,List.getElem_cons]

theorem after_other_input {h} (T : ContractionTree .atom (h+1)) (d : Nat) (i : Fin h) :
    afterTreeVertex T d (.input ⟨i.val+1,by simpa using i.succ.isLt⟩) = inputPort h i.succ := by
  change Port.map Sum.inl ((afterFrame h).sourcePort .tree _) = _
  simp [Net.sourcePort,afterFrame,afterSource,otherInputs,inputPort,Port.map,List.getElem_cons]
end Hypernets.Copying.Dereference
