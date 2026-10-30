import Hypernets.Copying.CopyingInputTree
import Hypernets.Copying.CopyFillingWitness
import Hypernets.Copying.SharingTreeAlgebra

/-! Literal two-copy endpoints. The second selected original input is copied
inside the retained branch of the first actual Figure 17 reduct. Both original
two-use distributors and every residual weakening remain in these graphs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble
open Graph

/-- Replace the retained branch of the literal two-branch copying construction.
The active payload and the full ordered term/atom output permutation stay fixed. -/
def copiesWith {d n k h} (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) :
    Hypernet d (List.replicate (n+2) .term) (environmentInterface (k*2) (h*2)) :=
  (Net.Parallel.net (Net.Tensor.family H K)
    (CopyRule.pairBoundary (n+1) k h) ⟨[false,true],by intro b; cases b <;> simp⟩).reboundary
      (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

/-- The original outer resource distributors follow the chosen retained branch. -/
def afterWith {d n k h} (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) :
    Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  Serial.net (copiesWith H K) (Translation.environmentDistributor d k h 2)

/-- Two literal copies, first at original input zero and then at original input
one. The latter is input zero of the first residual contraction tree. -/
noncomputable def afterSecond {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  afterWith H (CopyRule.after (CopyRule.residualTree T) H)

/-- Before the second step, this retained-branch construction is exactly the
first literal reduct, with no sharing-tree normalization. -/
theorem beforeSecond {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    afterWith H (CopyRule.before (CopyRule.residualTree T) H) = CopyRule.after T H := rfl

/-- Exchange the two selected original inputs, preserving every other position. -/
def exchangeInputs (n : Nat) : TypedPermutation (List.replicate (n+2) .term) :=
  CopyingInputPermutation.swap .term (n+2) ⟨0,by simp⟩ ⟨1,by simp⟩

/-- Perform the same two literal copies in the opposite order and restore the
original external input interface. This is the exact interchange endpoint. -/
noncomputable def opposite {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  CopyingInputPermutation.net
    (afterSecond (CopyingInputPermutation.reordered T (exchangeInputs n)) H)
    (exchangeInputs n)

end Hypernets.Copying.CopyingDouble
