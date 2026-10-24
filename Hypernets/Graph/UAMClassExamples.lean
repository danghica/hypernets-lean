import Hypernets.Graph.BehaviourIsoClosure
import Hypernets.Graph.SpecimenRelocationExamples
import Hypernets.Graph.UAMStructureExamples

/-! Nonempty compute behaviour and exact full-class executions. -/
namespace Hypernets.Linear.UAMClassExamples
open Graph

/-- The variable-removal regression still terminates in exactly two class steps. -/
theorem two_step_execution : ∃ t : State Examples.operations 0,
    (UAMClasses.machine (UAM.emptyBehaviour Examples.operations 0 (fun _ => .passive))).Steps 2
      (DeepStateClass.ofState UAMExamples.source) (DeepStateClass.ofState t) ∧
      DeepStateClass.Final (DeepStateClass.ofState t) := by
  obtain ⟨t,run,final⟩ := UAMExamples.terminates
  exact ⟨t,UAMClasses.project_steps _ run,final⟩

/-- Close the genuine singleton compute rule under all recursive state names. -/
def behaviour := UAMExamples.behaviour.isoClosure

/-- All compute successors lie in the class of the original fixed result. -/
theorem behaviour_deterministic : DeterministicModulo behaviour.step := by
  rintro s t u ⟨a,b,⟨_,rfl⟩,_,⟨bt⟩⟩ ⟨c,e,⟨_,rfl⟩,_,⟨bu⟩⟩
  exact ⟨bt.symm.trans bu⟩

/-- Every result is isomorphic to an initial state and is therefore rooted. -/
theorem behaviour_refocusing : RefocusingStates (fun _ => .active) behaviour.step := by
  rintro s t _ ⟨a,b,⟨_,rfl⟩,_,⟨iso⟩⟩
  exact DeepStateClass.initial_rooted (iso.initial_iff.mp (by exact ⟨rfl,trivial⟩))

/-- This nonempty full class machine is literally deterministic. -/
theorem deterministic : (UAMClasses.machine behaviour).Deterministic :=
  fun {_ _ _} l r => UAMClasses.deterministic behaviour
    UAMExamples.behaviour.isoClosure_invariant behaviour_deterministic l r

/-- The class machine includes the genuine extrinsic compute transition. -/
theorem compute_step : UAMClasses.Step behaviour (DeepStateClass.ofState UAMExamples.activeSource)
    (DeepStateClass.ofState Examples.initialValue) :=
  UAMClasses.project _ (.inr (UAMExamples.behaviour.into_isoClosure ⟨rfl,rfl⟩))

/-- Renaming closure has not altered the class transition relation. -/
theorem same_class_steps (s t : DeepStateClass Examples.operations 0) :
    UAMClasses.Step behaviour s t ↔ UAMClasses.Step UAMExamples.behaviour s t :=
  UAMExamples.behaviour.isoClosure_class_step

/-- A genuinely nested-hole specimen inhabits the new class-valued interface. -/
noncomputable def specimenSystem := ClassSpecimens.system DeepSpecimenExamples.template (fun _ => True)
  (UAM.emptyBehaviour DeepSpecimenExamples.ops 1 (fun _ => .passive))
  SpecimenRelocationExamples.allowed (DeepSpecimenExamples.template_closed 1) (fun _ h => False.elim h)

theorem initial_lifting :
    let D := DeepSpecimenExamples.specimen.relocate SpecimenRelocationExamples.allowed
      (TypedPosition.initial DeepSpecimenExamples.specimen.focus.underlying)
    specimenSystem.Lifting (DeepStateClass.ofState D.leftState) (DeepStateClass.ofState D.rightState) :=
  ClassSpecimens.initial_lifting _ _ _ SpecimenRelocationExamples.allowed
    (DeepSpecimenExamples.template_closed 1) (fun _ h => False.elim h) DeepSpecimenExamples.specimen
end Hypernets.Linear.UAMClassExamples
