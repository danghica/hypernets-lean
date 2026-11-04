import Hypernets.Copying.ParametricityCopyHost
import Hypernets.Copying.LambdaEntryCopyClassification
import Hypernets.Copying.LambdaEntryCopyRetained
import Hypernets.Copying.CopyingNormalMatch

/-! Complete forward and converse copying cases for the original Figure20
parametricity family, at every original recursive specimen. Retained/deep
payloads and every original shallow selected member are exhaustively covered. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyResidual
open Graph Opening Combined Search.Expansion
variable {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert free leftClosed rightClosed

/-- Every original copying rule occurrence has a proved opposite step and
original residual. The supplied contraction tree and full recursive payload
are arbitrary; shallow cases include every ordered large or small member. -/
theorem forward_case {m k h} (tree : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (f : Occurrence (CopyRule.before tree H) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨V,normal,g,input⟩ := CopyRule.normalized_occurrence tree H copyable f
  have token := input.trans attached
  let matched := ((CopyRule.localSuccessorMatch tree normal).map g).atToken token
  rcases LambdaEntryCopy.match_cases C cert template_lambdaEntries template_noOutputs leftClosed matched with
      ⟨retained,_⟩ | ⟨hole,name,i,n,orientation,spine,label,_,atToken,atOutput,_,_,_⟩
  · exact LambdaEntryCopy.retained_robust_case C cert template_lambdaEntries template_noOutputs
      free leftClosed rightClosed template_outputClosed tree normal g retained token Q P U step
  · obtain ⟨s,t,left,right,residual⟩ := CopyHost.any_hole_diagram C cert free leftClosed rightClosed
      (ContractionSpine.tree .term n orientation) spine hole name label i atOutput
    rw [atToken] at left right
    exact FillingWitness.matching_robust_case Q P U left right residual step

/-- The same exhaustive original-host analysis proves converse copying
robustness in the opposite specimen system, without a symmetry premise. -/
theorem converse_case {m k h} (tree : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (f : Occurrence (CopyRule.before tree H) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨V,normal,g,input⟩ := CopyRule.normalized_occurrence tree H copyable f
  have token := input.trans attached
  let matched := ((CopyRule.localSuccessorMatch tree normal).map g).atToken token
  rcases LambdaEntryCopy.match_cases C (fun e => (cert e).converse) converse_lambdaEntries
      converse_noOutputs rightClosed matched with
      ⟨retained,_⟩ | ⟨hole,name,i,n,orientation,spine,label,_,atToken,atOutput,_,_,_⟩
  · exact LambdaEntryCopy.retained_converse_robust_case C cert template_noOutputs
      free leftClosed rightClosed template_outputClosed converse_lambdaEntries
      tree normal g retained token Q P U step
  · obtain ⟨s,t,left,right,residual⟩ := CopyHost.any_hole_diagram C cert free leftClosed rightClosed
      (ContractionSpine.tree .term n orientation) spine hole name label i atOutput
    rw [atToken] at left right
    exact FillingWitness.matching_robust_case Q P U right left
      (FillingWitness.quasi_exchange _ residual) step

end Hypernets.Copying.Parametricity.CopyResidual
