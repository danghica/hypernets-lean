import Hypernets.Graph.StateQuotientBridge
import Hypernets.Transition

/-! Search-only machines and exact-length execution lifting between the two
state quotients. These machines do not include substitution or computation. -/
namespace Hypernets.Linear
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- The literal-label quotient equipped only with search transitions. -/
def StateClass.searchMachine (kind : Op → OperationKind) : Machine (StateClass ops d) where
  step := StateClass.Search kind
  final := StateClass.Final
  final_normal := StateClass.final_no_search

/-- The recursive quotient equipped only with search transitions. -/
def DeepStateClass.searchMachine (kind : Op → OperationKind) : Machine (DeepStateClass ops d) where
  step := DeepStateClass.Search kind
  final := DeepStateClass.Final
  final_normal := DeepStateClass.final_no_search

theorem StateClass.searchMachine_deterministic (kind : Op → OperationKind) :
    (searchMachine (ops := ops) (d := d) kind).Deterministic := by
  intro s t u h k
  exact search_deterministic h k

theorem DeepStateClass.searchMachine_deterministic (kind : Op → OperationKind) :
    (searchMachine (ops := ops) (d := d) kind).Deterministic := by
  intro s t u h k
  exact search_deterministic h k

namespace StateClass
variable {kind : Op → OperationKind}

/-- Projection preserves every finite search execution and its exact length. -/
theorem steps_toDeep {n} {s t : StateClass ops d}
    (run : (searchMachine kind).Steps n s t) :
    (DeepStateClass.searchMachine kind).Steps n (toDeep s) (toDeep t) := by
  induction run with
  | zero => exact .zero _
  | cons step _ ih => exact .cons (search_toDeep step) ih

/-- Every finite recursive search execution lifts from a specified literal class. -/
theorem steps_lift {n} (s : StateClass ops d) (t : DeepStateClass ops d)
    (run : (DeepStateClass.searchMachine kind).Steps n (toDeep s) t) :
    ∃ u, (searchMachine kind).Steps n s u ∧ toDeep u = t := by
  induction n generalizing s t with
  | zero =>
      have eq := run.zero_eq
      exact ⟨s, .zero _, eq⟩
  | succ n ih =>
      cases run with
      | cons step tail =>
          obtain ⟨u, first, hu⟩ := search_lift s _ step
          rw [← hu] at tail
          obtain ⟨v, rest, hv⟩ := ih u t tail
          exact ⟨v, .cons first rest, hv⟩

/-- Finite executions on the recursive quotient are exactly projected executions. -/
theorem steps_toDeep_iff {n} (s : StateClass ops d) (t : DeepStateClass ops d) :
    (DeepStateClass.searchMachine kind).Steps n (toDeep s) t ↔
      ∃ u, (searchMachine kind).Steps n s u ∧ toDeep u = t := by
  constructor
  · exact steps_lift s t
  · rintro ⟨u, run, rfl⟩
    exact steps_toDeep run

/-- Search termination at any prescribed exact length is preserved and reflected. -/
theorem final_run_toDeep_iff (n : Nat) (s : StateClass ops d) :
    (∃ t, (DeepStateClass.searchMachine kind).Steps n (toDeep s) t ∧ DeepStateClass.Final t) ↔
      ∃ u, (searchMachine kind).Steps n s u ∧ Final u := by
  constructor
  · rintro ⟨t, run, final⟩
    obtain ⟨u, lifted, hu⟩ := steps_lift s t run
    exact ⟨u, lifted, (final_toDeep u).mp (hu.symm ▸ final)⟩
  · rintro ⟨u, run, final⟩
    exact ⟨toDeep u, steps_toDeep run, (final_toDeep u).mpr final⟩

end StateClass
end Hypernets.Linear
