import Hypernets.Graph.StateSearch
import Hypernets.Graph.RealizationExamples

/-! Nonvacuous erasure-based state execution and recovery at an interior focus. -/
namespace Hypernets.Linear.Examples
open Graph

/-- The value edge survives erasure of its surrounding initial focus. -/
noncomputable def erasedValueOperation : SearchOperation initialValue.focussed.underlying where
  edge := ⟨.inl 0, by intro h; cases h⟩
  operation := Op.value
  label := rfl
  source := (State.coordinate initialValue).val.2
  arguments := []
  thunks := []
  source_eq := by
    change [FocusErasure.contract initialValue.focussed initialValue.focussed.targetVertex
      initialValue.focussed.targetVertex_spec initialValue.focussed.target] =
      [FocusErasure.position initialValue.focussed initialValue.focussed.targetVertex initialValue.focussed.targetVertex_spec]
    rw [initialValue.focussed.targetVertex_spec, FocusErasure.contract_target]
  target_eq := rfl
  arity := rfl

/-- The search relation on actual states executes the passive value rule and
reaches an actual final state. This is no longer merely an endpoint construction. -/
theorem value_state_search : ∃ t : State operations 0,
    State.Search (fun _ => .passive) initialValue t ∧ t.focussed.Final := by
  have step : SearchStep initialValue.focussed.underlying (fun _ => .passive)
      (State.coordinate initialValue).val
      (.backtrack, (State.coordinate initialValue).val.2) :=
    SearchStep.nullary erasedValueOperation rfl
  let q := (State.coordinate initialValue).advance step
  let result := q.realize initialValue.focussed.underlying_focusFree
    (initialValue.focussed.underlying_holeFree initialValue.hole_free)
  refine ⟨result, State.search_realize _ initialValue q step, ?_⟩
  apply (q.realize_boundary _ _).2.mpr
  exact ⟨rfl, ((State.coordinate_boundary initialValue).1.mpr value_boundary_states.1).2⟩

/-- Replace the old focus by a variable, obtaining a closed two-edge chain. -/
@[reducible] noncomputable def closedChain : Hypernet operations 0 [.term] [] :=
  initialValue.graph.relabelEdges (alphabet operations 0).signature
    (fun e => match e with
      | .inl _ => primitiveLabel operations 0 (.operation Op.value)
      | .inr _ => primitiveLabel operations 0 .variable)
    (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl)

theorem closedChain_focusFree : FocusFree closedChain := by
  intro e m eq
  cases e <;> cases eq

theorem closedChain_holeFree : HoleFree closedChain := by
  rintro h ⟨e, he⟩
  cases e <;> cases he

/-- A genuine state whose focus source is internal, after the variable edge. -/
noncomputable def interiorState : State operations 0 :=
  TypedPosition.realize (G := closedChain) ⟨(.search, .internal (.inr 0)), rfl⟩
    closedChain_focusFree closedChain_holeFree

theorem interior_state_not_initial : ¬ interiorState.focussed.Initial := fun h => h.2

/-- The interior state is recovered by erasure and reinsertion, with its focus
identified; the theorem applies to arbitrary input states of this representation. -/
noncomputable def interior_state_recovery :
    Focussed.Iso ((State.coordinate interiorState).realize interiorState.focussed.underlying_focusFree
      (interiorState.focussed.underlying_holeFree interiorState.hole_free)).focussed interiorState.focussed :=
  State.recover interiorState

end Hypernets.Linear.Examples
