import Hypernets.Copying.CopyingDoubleWitness

/-! The original copying reduct as a context in its retained branch, including
zero remaining inputs. The active payload and full resource distributors stay. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRetainedContext
open Graph
variable {d r k h : Nat}
    (H : Hypernet d [.term] (environmentInterface k h))

def copies (K : Hypernet d (List.replicate r .term) (environmentInterface k h)) :
    Hypernet d (List.replicate (r+1) .term) (environmentInterface (k*2) (h*2)) :=
  (Net.Parallel.net (Net.Tensor.family H K) (CopyRule.pairBoundary r k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩).reboundary
      (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

/-- This context accepts every original residual arity, including zero. -/
def after (K : Hypernet d (List.replicate r .term) (environmentInterface k h)) :
    Hypernet d (List.replicate (r+1) .term) (environmentInterface k h) :=
  Serial.net (copies H K) (Translation.environmentDistributor d k h 2)

/-- With the actual weakened original tree, the context is exactly the
unchanged original copying reduct. -/
theorem after_original (T : ContractionTree .term (r+1)) :
    after H (Serial.net (CopyRule.residual T d) H) = CopyRule.after T H := rfl

/-- Recursive paired residuals lift through the literal active copy and both
canonical output distributors. No transitivity of fillings is assumed. -/
noncomputable def witness {T : PreTemplate} (free : FocusFree H)
    {A B : Hypernet d (List.replicate r .term) (environmentInterface k h)}
    (w : FillingWitness T A B) : FillingWitness T (after H A) (after H B) := by
  apply FillingWitness.serial
  · apply FillingWitness.reboundary
    apply FillingWitness.parallel (CopyRule.pairBoundary r k h)
    intro b
    cases b
    · exact FillingWitness.refl H free
    · exact w
  · exact FillingWitness.refl (Translation.environmentDistributor d k h 2)
      (Translation.allLabels_tensor _
        (Distributor.allLabels_atDepth _ .term k 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))
        (Distributor.allLabels_atDepth _ .atom h 2 d (by intro m eq; cases eq) (by intro m eq; cases eq)))
end Hypernets.Copying.CopyingRetainedContext
