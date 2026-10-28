import Hypernets.Copying.ConverseSpecimenTransfer
import Hypernets.Copying.PrimitiveGuardedTransfer

/-! Actual retained right equality footprints yield quantitative residuals
for the opposite original specimen system. Footprint extraction is supplied
by the independently proved two-selected-input rematching construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert free leftClosed rightClosed

/-- A retained same-store occurrence retains the original Boolean result
and complete guarded output interface. Its residual uses original specimens. -/
theorem retained_same {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand R))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨right,left,residual⟩ := primitive_guarded_diamond C f (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.same tree d) (AtomEquality.Same.before_bindingGuarded tree d)
    (AtomEquality.Same.focusFree_sides tree d).2 (AtomEquality.Same.holeFree_sides tree d).2
    attached rfl (.local (.same tree d)) (PreTemplate.OutputClosed.converse (template_outputClosed kind))
    rightClosed leftClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (Specimens.converse_quasi (template_outputClosed kind) residual) step

/-- Distinct-store equality preserves both actual store outputs, with the
unchanged false-result rule and an original opposite quasi-specimen. -/
theorem retained_different {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (AtomEquality.Different.before tree other d) (C.expand R))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨right,left,residual⟩ := primitive_guarded_diamond C f (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.different tree other d) (AtomEquality.Different.before_bindingGuarded tree other d)
    (AtomEquality.Different.focusFree_sides tree other d).2 (AtomEquality.Different.holeFree_sides tree other d).2
    attached rfl (.local (.different tree other d)) (PreTemplate.OutputClosed.converse (template_outputClosed kind))
    rightClosed leftClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (Specimens.converse_quasi (template_outputClosed kind) residual) step
end Hypernets.Copying.OperationalTemplates.ConverseResidual
