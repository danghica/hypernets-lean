import Hypernets.Graph.LocalRewiring
import Hypernets.Graph.SpecimenTraversalExamples

/-! Direct original-graph interactions and their actual-state successors. -/
namespace Hypernets.Linear.LocalSearchExamples
open Graph

/-- The actual value edge, before erasure, is adjacent to the initial focus. -/
noncomputable def valueOperation : SearchOperation Examples.initialValue.graph where
  edge := .inl 0
  operation := Examples.Op.value
  label := rfl
  source := Examples.initialValue.focussed.target
  arguments := []
  thunks := []
  source_eq := by
    change [FocusInsertion.split Examples.value (.input 0) (.input 0)] =
      [FocusInsertion.fresh Examples.value]
    simp [FocusInsertion.split]
  target_eq := rfl
  arity := rfl

/-- A passive nullary operation selects the old target; joining it returns to
its source. This tests the nontrivial join case rather than an unaffected port. -/
theorem value_interaction :
    LocalInteraction Examples.initialValue.focussed (fun _ => .passive)
      (.backtrack,Examples.initialValue.focussed.target) :=
  .enter valueOperation rfl rfl

/-- The independent incidence presentation has a genuine terminating step. -/
theorem value_terminates : ∃ t : State Examples.operations 0,
    State.IncidenceSearch (fun _ => .passive) Examples.initialValue t ∧ t.focussed.Final := by
  obtain ⟨t,step,final⟩ := Examples.value_state_search
  exact ⟨t,State.search_iff_incidence.mp step,final⟩

/-- Insert a search focus before the variable in the closed variable/value chain. -/
noncomputable def initialChain : State Examples.operations 0 :=
  (TypedPosition.initial Examples.closedChain).realize
    Examples.closedChain_focusFree Examples.closedChain_holeFree

/-- The variable trigger is checked directly on the actual graph's source list. -/
theorem variable_interaction :
    LocalInteraction initialChain.focussed (fun _ => .passive)
      (.rewrite,initialChain.focussed.source) := by
  apply LocalInteraction.trigger (f := initialChain.focussed) (.inl (.inr 0)) rfl rfl
  simp [initialChain,TypedPosition.initial,TypedPosition.realize,Examples.closedChain,
    Net.relabelEdges,Examples.initialValue,FocusInsertion.insert,FocusInsertion.source,
    FocusInsertion.split,FocusInsertion.focussed,FocusInsertion.host,Port.map]

/-- A variable trigger produces an actual rewrite-mode state by the independent
incidence rules, without postulating a substitution step. -/
theorem variable_successor : ∃ t : State Examples.operations 0,
    State.IncidenceSearch (fun _ => .passive) initialChain t ∧ t.focussed.mode = .rewrite := by
  let p := (Focus.rewrite,initialChain.focussed.source)
  have step := variable_interaction.sound
  let q : TypedPosition initialChain.focussed.underlying :=
    ⟨_,step.preserves_term initialChain.focussed.coordinate.property⟩
  refine ⟨q.realize _ _,⟨p,variable_interaction,⟨LocalRewiring.canonical initialChain p q rfl⟩⟩,rfl⟩

end Hypernets.Linear.LocalSearchExamples
