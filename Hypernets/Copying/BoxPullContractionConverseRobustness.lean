import Hypernets.Copying.BoxPullContractionConverseTransport
import Hypernets.Copying.BoxPullContractionConverseResidual

/-! Universal converse BPullC robustness. Actual left enabledness and proved
successor coherence let the forward geometric residual handle every supplied
right successor, with the exact sharing correction used in the opposite direction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined

/-- Full converse robustness for all original recursive BPullC specimens and
all original local rules. No matching, decomposition, or robustness hypothesis
is present: exact original matching rewrites and residuals are constructed. -/
theorem template_robust_converse (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust Q P U := by
  intro S _ _ mode _ u next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  change StateClass.machine.step (StateClass.ofState S.rightState) u at next
  rw [rightEq] at next
  obtain ⟨H,w,rightStep,_⟩ := BoxPermutation.class_rewrite next
  obtain ⟨A,a,leftStep⟩ := filling_enabled_converse S.context S.edges S.right_closed S.free rightStep
  obtain ⟨B,b,matchedRight,⟨residual⟩⟩ := filling_rewrite S.context S.edges S.free leftStep
  have quasi := residual.opposite_quasi (rewrite_holeFree leftStep S.left_closed)
    (rewrite_endpoints_term leftStep).2 P U
  have eq := StateClass.machine_deterministic next (StateClass.project (.lift (.rewrite matchedRight)))
  apply Or.inr
  change ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
    StateClass.machine.Steps l (StateClass.ofState S.leftState) y ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) x y
  rw [leftEq,eq]
  exact ⟨0,1,_,_,Q.refl 1,.zero _,
    .cons (StateClass.project (.lift (.rewrite leftStep))) (.zero _),quasi⟩
end Hypernets.Copying.BoxPullContraction
