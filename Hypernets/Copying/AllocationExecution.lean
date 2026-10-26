import Hypernets.Copying.AllocationSafety

/-! An explicit search/allocation subsystem. Other copying and compute rules are
not supplied here; this is not an Execution instance for observational equivalence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Allocation
open Graph

/-- A graph-changing state keeps the actual graph and its token coordinate together. -/
abbrev State (d : Nat) (O : List Wire) := Σ G : Hypernet d [.term] O, Search.Position G

/-- Search plus the allocation compute rule at the root, optionally followed by an
unchanged serial continuation. The stable premise is retained in both cases. -/
inductive Step {d O} : State d O → State d O → Prop where
  | search (G : Hypernet d [.term] O) {s t} (h : Search.Step G s t) : Step ⟨G,s⟩ ⟨G,t⟩
  | allocate (G : Hypernet d [.term] O) (stable : Stable G) :
      Step ⟨before G,(.rewrite,.input 0)⟩ ⟨after G,(.search,.input 0)⟩
  | allocate_suffix {J} (G : Hypernet d [.term] J) (stable : Stable G) (K : Hypernet d J O) :
      Step ⟨Serial.net (before G) K,(.rewrite,.input 0)⟩
        ⟨Serial.net (after G) K,(.search,.input 0)⟩

/-- Returning to the external input is normal even after allocation is added. -/
theorem completed_normal {d O} {s : State d O} (done : Search.Completed s.2) :
    ∀ t, ¬ Step s t := by
  intro t h
  cases h with
  | @search G s t h =>
    rcases done with ⟨mode,input⟩
    rcases s with ⟨m,v⟩
    simp only at mode input
    subst m
    exact Search.final_no_step input h
  | allocate => cases done.1
  | allocate_suffix => cases done.1

/-- A genuine subsystem machine, with finality proved rather than assumed. -/
def machine (d : Nat) (O : List Wire) : Machine (State d O) where
  step := Step
  final s := Search.Completed s.2
  final_normal h := completed_normal h _

/-- Search returns the newly allocated instance even with the untouched continuation. -/
theorem returns_suffix {d J O} (G : Hypernet d [.term] J) (K : Hypernet d J O) :
    Search.Step (Serial.net (after G) K) (.search,.input 0) (.backtrack,.input 0) := by
  apply Search.instance_return (Serial.leftEdge (after G) K (instanceEdge G)) _
  · exact (Serial.leftEdge_label _ _ _).trans (instance_label G)
  · cases d <;> change (.input 0 : (Serial.net (after G) K).Vertex) ∈ [.input 0]
    all_goals exact List.mem_cons_self

/-- The literal constant translation, including its empty environment distributors. -/
def constantArgument (n : Nat) := Translation.term (Term.const (k := 0) (h := 0) (.nat n))

theorem constantArgument_stable (n : Nat) : Stable (constantArgument n) := by
  apply Stable.of_labels
  rintro ⟨b,e⟩
  cases b with
  | false =>
    rcases e with ⟨c,e⟩
    cases c with
    | false => exact Fin.elim0 e.1
    | true => exact ⟨.operation (.const (.nat n)),rfl,rfl⟩
  | true => exact Fin.elim0 e.1

/-- The original translated ref expression; no translation clause is simplified. -/
def referenceGraph (n : Nat) := Translation.term (Term.unary (k := 0) (h := 0) .ref (.const (.nat n)))

/-- The post-allocation graph retains the same single-use distributors as the source. -/
def allocatedGraph (n : Nat) := Serial.net (after (constantArgument n)) (Translation.singleUse 0 0 0)

def referenceHead (n : Nat) : (referenceGraph n).Edge := ⟨false,⟨false,(0 : Fin 1)⟩⟩
def referenceValue (n : Nat) : (referenceGraph n).Edge := ⟨false,⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩⟩
def referenceArgument (n : Nat) : (referenceGraph n).Vertex :=
  (referenceGraph n).targetPort (referenceHead n) (0 : Fin 1)

/-- Evaluation first searches the ref argument. -/
theorem reference_enter (n : Nat) :
    Search.Step (referenceGraph n) (.search,.input 0) (.search,referenceArgument n) := by
  apply Search.Step.search (referenceHead n) (.operation (.unary .ref)) _ _ rfl
  · change (.input 0 : (referenceGraph n).Vertex) ∈ [.input 0]; exact List.mem_cons_self
  · rfl

/-- The unchanged literal argument returns as a value. -/
theorem reference_value (n : Nat) :
    Search.Step (referenceGraph n) (.search,referenceArgument n) (.backtrack,referenceArgument n) := by
  apply Search.Step.search (referenceValue n) (.operation (.const (.nat n))) _ _ rfl
  · change referenceArgument n ∈ [referenceArgument n]; exact List.mem_cons_self
  · rfl

/-- Backtracking through ref triggers its compute rule. -/
theorem reference_ready (n : Nat) :
    Search.Step (referenceGraph n) (.backtrack,referenceArgument n) (.rewrite,.input 0) :=
  .backtrack (referenceHead n) (.unary .ref) (.input 0) _ 0 _ rfl rfl (by decide) rfl rfl

/-- A five-transition execution: three search steps, allocation, then instance return. -/
theorem reference_run (n : Nat) :
    (machine 0 []).Steps 5 ⟨referenceGraph n,(.search,.input 0)⟩
      ⟨allocatedGraph n,(.backtrack,.input 0)⟩ :=
  .cons (.search _ (reference_enter n)) (.cons (.search _ (reference_value n))
    (.cons (.search _ (reference_ready n))
      (.cons (.allocate_suffix (constantArgument n) (constantArgument_stable n) (Translation.singleUse 0 0 0))
        (.cons (.search _ (returns_suffix _ _)) (.zero _)))))

/-- The endpoint is a successful value, not merely suspension at rewrite focus. -/
theorem reference_completes (n : Nat) :
    (machine 0 []).final ⟨allocatedGraph n,(.backtrack,.input 0)⟩ := ⟨rfl,trivial⟩
end Hypernets.Copying.Allocation
