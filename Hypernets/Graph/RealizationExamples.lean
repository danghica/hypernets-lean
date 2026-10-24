import Hypernets.Graph.SearchRealization
import Hypernets.Graph.SearchExamples

/-! Actual initial/final states and an interior-vertex insertion regression. -/
namespace Hypernets.Linear.Examples
open Graph

theorem value_focusFree : FocusFree value := by
  intro e m bad
  cases bad

/-- Initial attachment to the existing value graph creates an actual state. -/
noncomputable def initialValue : State operations 0 :=
  (TypedPosition.initial value).realize value_focusFree value_holeFree

/-- The passive nullary search step has a typed target and an explicit final state. -/
noncomputable def finalValue : State operations 0 :=
  ((TypedPosition.initial value).advance SearchExamples.value_finishes).realize
    value_focusFree value_holeFree

theorem value_boundary_states : initialValue.focussed.Initial ∧ finalValue.focussed.Final :=
  ⟨⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩

/-- The inserted focus is a new edge, even at a boundary vertex. -/
theorem initial_value_has_distinct_endpoints :
    initialValue.focussed.source ≠ initialValue.focussed.target :=
  initialValue.focussed.self_acyclic

theorem twoHoles_focusFree : FocusFree twoHoles := by
  intro e m bad
  cases bad

/-- Interior insertion changes the next edge's source, leaving the preceding
edge's target at the old vertex. The new focus connects these distinct vertices. -/
theorem interior_insertion :
    let inserted := FocusInsertion.insert twoHoles (.internal 0) rfl (by intro h; cases h) .search
    inserted.target (.inl 0) = [FocusInsertion.host twoHoles (.internal 0)] ∧
    inserted.source (.inl 1) = [FocusInsertion.fresh twoHoles] ∧
    inserted.source (.inr 0) = [FocusInsertion.host twoHoles (.internal 0)] ∧
    inserted.target (.inr 0) = [FocusInsertion.fresh twoHoles] := by
  simp [FocusInsertion.insert, FocusInsertion.source, FocusInsertion.target,
    FocusInsertion.split, twoHoles]

/-- A focus at that interior vertex is not mistaken for an initial focus. -/
theorem interior_not_initial :
    ¬ (FocusInsertion.focussed twoHoles (.internal 0) rfl (by intro h; cases h)
      .search twoHoles_focusFree).Initial := by
  intro h
  exact h.2

end Hypernets.Linear.Examples
