import Hypernets.Copying.PointedRewriteTransport

/-! Full forward and converse BPerm robustness for the original concrete
copying UAM and original recursively filled specimens. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

/-- Original specimen coordinates supply a pointed filling without extra hypotheses. -/
def specimenPointed (S : Specimen template Specimens.allContexts) :
    PointedFilling (S.context.expand S.left) (Net.Expansion.host S.context S.left S.token.2)
      (S.context.expand S.right) (Net.Expansion.host S.context S.right S.token.2) where
  filling := ⟨S.context,S.free,S.left,S.right,S.edges,DeepIso.refl _,DeepIso.refl _⟩
  point := S.token.2
  left := by cases S.token.2 <;> rfl
  right := by cases S.token.2 <;> rfl

/-- A step from rewrite mode reflects to the actual original graph rewrite at
exactly the supplied finite depth. -/
theorem class_rewrite {d} {G : Hypernet d [.term] []} {v} {t}
    (next : StateClass.machine.step (StateClass.ofState ⟨d,G,(.rewrite,v)⟩) t) :
    ∃ H w, Rewrite G v H w ∧ t = StateClass.ofState ⟨d,H,(.search,w)⟩ := by
  obtain ⟨u,step,eq⟩ := StateClass.reflect next
  cases step with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite r => exact ⟨_,_,r,eq⟩

/-- Every forward case uses zero extra left steps and one actual right rewrite,
followed by a genuine original quasi-specimen. -/
theorem template_robust (Q P R : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust Q P R := by
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
  obtain ⟨A,a,leftStep,eq⟩ := class_rewrite next
  obtain ⟨B,b,rightStep,⟨residual⟩⟩ := (specimenPointed S).rewrite leftStep
  have quasi := residual.quasi (rewrite_holeFree leftStep S.left_closed)
    (rewrite_holeFree rightStep S.right_closed) (rewrite_endpoints_term leftStep).2
  have result := FillingWitness.matching_robust_case Q P R
    (StateClass.project (.lift (.rewrite leftStep)))
    (StateClass.project (.lift (.rewrite rightStep))) quasi next
  apply Or.inr
  change ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
    StateClass.machine.Steps l (StateClass.ofState S.rightState) b ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b
  rw [rightEq]
  exact result

/-- Every converse case is obtained by constructing reversed source and residual
fillings, while the quasi-specimen is returned in the original orientation. -/
theorem template_robust_converse (Q P R : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust Q P R := by
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
  obtain ⟨B,b,rightStep,eq⟩ := class_rewrite next
  obtain ⟨A,a,leftStep,⟨residual⟩⟩ := (specimenPointed S).rewrite_converse rightStep
  have quasi := FillingWitness.quasi_exchange _ (residual.quasi
    (rewrite_holeFree leftStep S.left_closed) (rewrite_holeFree rightStep S.right_closed)
    (rewrite_endpoints_term leftStep).2)
  have result := FillingWitness.matching_robust_case Q P R
    (StateClass.project (.lift (.rewrite rightStep)))
    (StateClass.project (.lift (.rewrite leftStep))) quasi next
  apply Or.inr
  change ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
    StateClass.machine.Steps l (StateClass.ofState S.leftState) b ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b
  rw [leftEq]
  exact result
end Hypernets.Copying.BoxPermutation
