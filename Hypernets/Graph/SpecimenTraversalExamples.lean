import Hypernets.Graph.SpecimenTraversal
import Hypernets.Graph.DeepSpecimenExamples

/-! Traversal of the original deep-filled specimen, and a rootedness regression. -/
namespace Hypernets.Linear.SpecimenTraversalExamples
open Graph DeepSpecimenExamples

/-- All holes are inside a box, so the original outer focus is neither entering
nor exiting; this is independent of its search mode. -/
theorem no_boundaries : ¬ specimen.focus.Entering ∧ ¬ specimen.focus.Exiting := by
  constructor
  · rintro ⟨e,h,label,_⟩; exact context_no_shallow_hole e h label
  · rintro ⟨e,h,label,_⟩; exact context_no_shallow_hole e h label

theorem away : ¬ ExpansionSearch.HoleBoundary specimen.focus.underlying specimen.focus.coordinate.val := by
  intro h
  rcases specimen.focus.boundary_iff.mp h with ⟨_,h⟩ | ⟨_,h⟩
  · exact no_boundaries.1 h
  · exact no_boundaries.2 h

/-- The consumer remains an actual operation in the erased context. -/
noncomputable def consumer : SearchOperation specimen.focus.underlying where
  edge := ⟨.inl .stop,by intro eq; cases eq⟩
  operation := false
  label := rfl
  source := specimen.focus.coordinate.val.2
  arguments := []
  thunks := []
  source_eq := by
    have src : context.source (.inl .stop) = [specimen.focus.target] := by
      simp [context,FocusInsertion.insert,FocusInsertion.source,FocusInsertion.split,
        FocusInsertion.fresh,specimen,focus,FocusInsertion.focussed]
    change (context.source (.inl .stop)).map (FocusErasure.contract specimen.focus
      specimen.focus.targetVertex specimen.focus.targetVertex_spec) = _
    rw [src]
    change [FocusErasure.contract specimen.focus specimen.focus.targetVertex
      specimen.focus.targetVertex_spec specimen.focus.target] = [_]
    rw [specimen.focus.targetVertex_spec, FocusErasure.contract_target]
    rfl
  target_eq := rfl
  arity := rfl

noncomputable def returned : TypedPosition specimen.focus.underlying :=
  ⟨(.backtrack,specimen.focus.coordinate.val.2),specimen.focus.coordinate.property⟩

theorem context_step : SearchStep specimen.focus.underlying (fun _ => .passive)
    specimen.focus.coordinate.val returned.val := SearchStep.nullary consumer rfl

/-- Actual expansion of the already focussed deep context makes the predicted step. -/
theorem actual_step : State.Search (fun _ => .passive) specimen.leftState (specimen.leftAt returned) :=
  (specimen.left_search_iff away _ _).mpr ⟨returned,context_step,⟨Focussed.Iso.refl _⟩⟩

/-- Any recursively renamed successor has the same context-coordinate witness. -/
theorem matching {target : State ops 1}
    (step : State.DeepSearch (fun _ => .passive) specimen.leftState target) :
    Nonempty (Focussed.DeepIso (specimen.leftAt returned).focussed target.focussed) ∧
      State.DeepSearch (fun _ => .passive) specimen.rightState (specimen.rightAt returned) := by
  obtain ⟨q,h,iso⟩ := (specimen.left_deepSearch_iff away _ target).mp step
  have eq : q = returned := Subtype.ext (SearchStep.deterministic h context_step)
  subst q
  exact ⟨iso,(specimen.right_deepSearch_iff away _ _).mpr
    ⟨returned,context_step,⟨Focussed.DeepIso.refl _⟩⟩⟩

/-- The bridge does not accidentally make this previously non-rooted deep
specimen reachable from the initial input of its erased context. -/
theorem no_initial_context_run (kind : Bool → OperationKind) (n : Nat) :
    ¬ (coordinateMachine specimen.focus.underlying kind).Steps n
      (TypedPosition.initial specimen.focus.underlying).val specimen.focus.coordinate.val := by
  intro run
  obtain ⟨left,right⟩ := specimen.rooted_of_context_run run
  rcases specimen_not_rooted kind with bad | bad
  · exact bad left
  · exact bad right

end Hypernets.Linear.SpecimenTraversalExamples
