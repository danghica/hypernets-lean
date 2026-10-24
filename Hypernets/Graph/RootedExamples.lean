import Hypernets.Graph.ConcreteRefocusing
import Hypernets.Graph.DeepSearchExamples

/-! Rooted successful search and a non-rooted interior focus behind a variable. -/
namespace Hypernets.Linear.Examples
open Graph

/-- Actual initial states satisfy the concrete rooted predicate. -/
theorem initial_value_rooted (kind : Op → OperationKind) : State.Rooted kind initialValue :=
  DeepStateClass.initial_rooted (s := DeepStateClass.ofState initialValue) value_boundary_states.1

/-- The successful passive value search yields a rooted final state. -/
theorem final_value_rooted : State.Rooted (fun _ => .passive) finalValue :=
  DeepStateClass.rooted_steps (initial_value_rooted _) value_deep_run

/-- The existing interior-focus example is well-formed but never rooted:
a variable edge, rather than an operation, lies immediately before its focus. -/
theorem interior_state_not_rooted (kind : Op → OperationKind) : ¬ State.Rooted kind interiorState := by
  apply State.not_rooted_of_path (s := interiorState)
    (Net.Path.single (Sum.inl (Sum.inr 0))) (by rfl)
  · change FocusInsertion.host closedChain (.internal (.inr 0)) ∈
      (closedChain.target (.inr 0)).map (FocusInsertion.host closedChain)
    exact List.mem_map.mpr ⟨.internal (.inr 0), by exact List.mem_singleton_self _, rfl⟩
  · exact List.mem_singleton_self _
  · change ¬ IsOperation operations 0 (primitiveLabel operations 0 .variable)
    exact id

end Hypernets.Linear.Examples
