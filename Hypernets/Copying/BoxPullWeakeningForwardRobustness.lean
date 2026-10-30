import Hypernets.Copying.BoxPullWeakeningForwardTransport
import Hypernets.Copying.FullBPermRobustness

/-! Universal forward BPullW robustness for the original copying UAM. The
copying case uses its two proved Idem corrections as exact refinements, while
all source decompositions and local rewrites are constructed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

/-- Every original recursive BPullW specimen has the required actual matching
rewrite. Deep and shallow overlaps are exhaustive; the original quasi-specimen
uses only the independently proved Idem equivalences after its residual. -/
theorem template_robust (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust Q P U := by
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
  change StateClass.machine.step (StateClass.ofState S.leftState) u at next
  rw [leftEq] at next
  obtain ⟨A,a,leftStep,eq⟩ := BoxPermutation.class_rewrite next
  obtain ⟨B,b,rightStep,⟨residual⟩⟩ := filling_rewrite S.context S.edges S.free leftStep
  have quasi := residual.quasi (rewrite_holeFree leftStep S.left_closed)
    (rewrite_endpoints_term leftStep).2 P U
  apply Or.inr
  change ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
    StateClass.machine.Steps l (StateClass.ofState S.rightState) y ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) x y
  rw [rightEq,eq]
  exact ⟨0,1,_,_,Q.refl 1,.zero _,
    .cons (StateClass.project (.lift (.rewrite rightStep))) (.zero _),quasi⟩

end Hypernets.Copying.BoxPullWeakening
