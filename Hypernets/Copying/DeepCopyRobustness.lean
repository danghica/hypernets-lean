import Hypernets.Copying.FramedFillingTransfer

/-! Concrete equality-up-to residuals and the full robustness conclusion for
closed all-deep copying cases. Arbitrary surrounding cases use framed transfer;
this is not yet a proof classifying every BPerm specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.DeepCopy
open Graph Combined

/-- The actual lambda construction retains global hole freedom. -/
theorem payload_closed {d k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (closed : HoleFree B) : HoleFree (lambdaPayload B) :=
  Serial.holeFree_net (Translation.allLabels_primitive _ _ _ (by intro h eq; cases eq))
    (by intro e; exact (Translation.allLabels_cast _ rfl _ B).mpr closed)

variable {d} (T : ContractionTree .term 1)
    {B C : Hypernet d [.term] (environmentInterface 1 0)}

def source (B : Hypernet d [.term] (environmentInterface 1 0)) : UnboundedState :=
  ⟨d+1,CopyRule.before T (lambdaPayload B),(.rewrite,.input 0)⟩
def target (B : Hypernet d [.term] (environmentInterface 1 0)) : UnboundedState :=
  ⟨d+1,CopyRule.after T (lambdaPayload B),(.search,.input 0)⟩

/-- These are original full-machine transitions, projected to representation classes. -/
theorem step (B : Hypernet d [.term] (environmentInterface 1 0)) :
    StateClass.machine.step (StateClass.ofState (source T B)) (StateClass.ofState (target T B)) :=
  StateClass.project (.lift (Combined.local_step (.copy T _ (.lambda B))))

/-- No semantic template hypothesis is used to construct the equality-up-to residual. -/
theorem quasi (w : FillingWitness template B C) (left : HoleFree B) (right : HoleFree C) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq
      (StateClass.ofState (target T B)) (StateClass.ofState (target T C)) :=
  (w.deepCopy T).initial_quasi template_outputClosed
    (CopyRule.holeFree_after T _ (payload_closed left))
    (CopyRule.holeFree_after T _ (payload_closed right))

theorem quasi_opposite (w : FillingWitness template B C) (left : HoleFree B) (right : HoleFree C) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi Eq Eq
      (StateClass.ofState (target T C)) (StateClass.ofState (target T B)) :=
  (w.deepCopy T).quasi_opposite template_outputClosed
    (CopyRule.holeFree_after T _ (payload_closed left))
    (CopyRule.holeFree_after T _ (payload_closed right)) (.search,.input 0) rfl (by intro eq; cases eq)

/-- The entire forward robustness conclusion for this case, for every cost
preorder triple and every independently presented successor of the left state. -/
theorem robust_case (w : FillingWitness template B C) (Q P R : CostOrder) (left : HoleFree B) (right : HoleFree C)
    {u} (next : StateClass.machine.step (StateClass.ofState (source T B)) u) :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
      StateClass.machine.Steps l (StateClass.ofState (source T C)) b ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b :=
  FillingWitness.matching_robust_case Q P R (step T B) (step T C) (quasi T w left right) next

/-- The converse uses the same residual certificate with the specimen projections exchanged. -/
theorem robust_case_opposite (w : FillingWitness template B C) (Q P R : CostOrder) (left : HoleFree B) (right : HoleFree C)
    {u} (next : StateClass.machine.step (StateClass.ofState (source T C)) u) :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
      StateClass.machine.Steps l (StateClass.ofState (source T B)) b ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b :=
  FillingWitness.matching_robust_case Q P R (step T C) (step T B) (quasi_opposite T w left right) next
end Hypernets.Copying.BoxPermutation.DeepCopy
