import Hypernets.Copying.NullaryDeepLocal
import Hypernets.Copying.AllContextResiduals

/-! Quantitative beta and copying cases for all-context nullary robustness.
Actual matching rewrites and their pointed residual specimens are constructed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.NullaryResidual
open Graph Combined RetainedFootprint

/-- Every actual beta occurrence admits a paired original rule and an exact
residual. No bound is imposed on the paired body or surrounding context. -/
theorem beta {T : PreTemplate} {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs) (padding : T.PaddingClosed)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {k h K} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts none.outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have avoid := NullaryOverlap.beta_avoids C cert none leftClosed B G stable f attached
  obtain ⟨H,paired,⟨w⟩⟩ := beta_local C cert none padding free leftClosed B G stable f avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f cert avoid free 0 rfl
    (.local (.beta B G stable)) paired w attached none.outputClosed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

/-- The actual selected spine is rematched inside any supplied copying tree;
unused siblings remain untouched. Every original copyable payload is covered. -/
theorem copying {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts none.outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨m,orientation,H,copyable,g,token,avoid⟩ :=
    NullaryOverlap.minimal_copy_occurrence C cert none free leftClosed tree copyable f attached
  let spine := ContractionSpine.tree .term m orientation
  obtain ⟨K,paired,⟨w⟩⟩ := copying_local C cert none free leftClosed spine H copyable g avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C g cert avoid free ⟨0,by simp⟩
    (List.getElem_replicate _) (.local (.copy spine H copyable)) paired w token none.outputClosed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step
end Hypernets.Copying.NullaryResidual
