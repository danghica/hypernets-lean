import Hypernets.Copying.ConverseCopyFootprint
import Hypernets.Copying.ConverseDeepExtraction
import Hypernets.Copying.ConverseSpecimenTransfer

/-! Universal copying residual case from an actual right local occurrence.
The selected minimal spine is constructed, its entire footprint is proved
retained, and its actual paired steps have an original opposite quasi-specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert free away leftClosed rightClosed

/-- No restriction is imposed on unused branches of the supplied tree.
Rematching and residual admissibility are proved from the original specimen. -/
theorem copying_diamond {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand R))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v) :
    ∃ H K : Hypernet d [.term] [], ∃ a b,
      Rewrite (C.expand R) (Net.Expansion.host C R v) H a ∧
      Rewrite (C.expand L) (Net.Expansion.host C L v) K b ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi Eq Eq
        (StateClass.ofState ⟨d,H,(.search,a)⟩) (StateClass.ofState ⟨d,K,(.search,b)⟩) := by
  let rev := fun e => (cert e).converse
  obtain ⟨m,orientation,P,copyable,g,token,avoid⟩ :=
    BindingOverlap.minimal_copy_occurrence C rev free away tree copyable f attached
  let spine := ContractionSpine.tree .term m orientation
  obtain ⟨H,step,⟨w,binding,shallow⟩⟩ := copying_local C cert free rightClosed spine P copyable g avoid
  have graft := residualGraft_binding_open_guarded C g rev avoid free (CopyRule.before_bindingGuarded spine copyable)
    w binding shallow
  obtain ⟨right,left,residual⟩ := converse_input_diamond C g cert avoid free.1 ⟨0,by simp⟩ (List.getElem_replicate _)
    (.local (.copy spine P copyable)) step w graft token (template_outputClosed kind) leftClosed rightClosed
  exact ⟨_,_,_,_,right,left,residual⟩

/-- Every actual right copying successor satisfies the original quantitative
converse clause, independently of its supplied tree presentation or reduct. -/
theorem copying {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand R))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,K,a,b,right,left,residual⟩ := copying_diamond C cert free away leftClosed rightClosed tree G copyable f attached
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left))) residual step
end Hypernets.Copying.OperationalTemplates.ConverseResidual
