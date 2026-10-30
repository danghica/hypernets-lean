import Hypernets.Copying.CopyingTemplateInputSafety
import Hypernets.Copying.CopyingSelectedInput

/-! The original two-copy diagram with the first copy at an arbitrary
positive input and the next copy at input zero. All permutations are actual
common graph contexts, and the residual keeps the original directed template. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingSelectedInput.OtherZero
open Graph Combined CopyingInputPermutation
open BoxPullWeakening (PointedWitness)
variable {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))
    (i : Fin (List.replicate (n+2) Wire.term).length)

noncomputable def tree : ContractionTree .term (n+2) := reordered T (permutation i)
noncomputable def leftAfter := net (CopyingDoubleAt.leftAfter (tree T i) H i) (permutation i).symm
noncomputable def rightAfter := net (CopyingDoubleAt.rightAfter (tree T i) H i) (permutation i).symm

theorem selected_zero : (permutation i).bijection.invFun i = ⟨0,by simp⟩ := by
  simp only [permutation,swap,exchange]
  by_cases zero : i = ⟨0,by simp⟩
  · subst i; simp
  · simp

/-- The zero-input copy is an actual original rewrite of the unmodified source. -/
theorem left_rewrite (copyable : Copyable H) :
    Rewrite (CopyRule.before T H) (.input ⟨0,by simp⟩)
      (leftAfter T H i) (.input ⟨0,by simp⟩) := by
  have step := CopyingInputPermutation.rewrite (permutation i).symm i i
    (CopyingDoubleAt.left_rewrite (tree T i) H i copyable)
  change Rewrite _ (.input ((permutation i).bijection.invFun i)) _
    (.input ((permutation i).bijection.invFun i)) at step
  rw [selected_zero] at step
  exact step.rename (beforeIso T H (permutation i)).symm (DeepIso.refl _)

/-- After the first positive-input copy, the same zero input still has an
actual original copy. This includes the entire original residual tree. -/
theorem right_rewrite (copyable : Copyable H) (positive : 0 < i.val) :
    Rewrite (CopyingSelectedInput.after T H i) (.input ⟨0,by simp⟩)
      (rightAfter T H i) (.input ⟨0,by simp⟩) := by
  have step := CopyingInputPermutation.rewrite (permutation i).symm i i
    (CopyingDoubleAt.right_rewrite (tree T i) H i copyable positive)
  change Rewrite _ (.input ((permutation i).bijection.invFun i)) _
    (.input ((permutation i).bijection.invFun i)) at step
  rw [selected_zero] at step
  exact step

/-- The original copying residual and its independently proved sharing
correction survive the compensating full-interface permutation. -/
noncomputable def residual (copyable : Copyable H) (free : FocusFree H) :
    CopyingTemplate.Residual (leftAfter T H i) (.input ⟨0,by simp⟩)
      (rightAfter T H i) (.input ⟨0,by simp⟩) := {
  middle := net
    (net (CopyingDouble.opposite (CopyingDoubleAt.normalized (tree T i) i) H)
      (CopyingDoubleAt.ordering i).symm) (permutation i).symm
  point := .input ⟨0,by simp⟩
  paired := PointedWitness.input
    (((CopyingDouble.oppositeWitness (CopyingDoubleAt.normalized (tree T i) i) H copyable free).inputPermutation
      (CopyingDoubleAt.ordering i).symm).inputPermutation (permutation i).symm) ⟨0,by simp⟩
  correction := PointedWitness.input
    (((CopyingDouble.interchange (CopyingDoubleAt.normalized (tree T i) i) H free).reverseSharing.inputPermutation
      (CopyingDoubleAt.ordering i).symm).inputPermutation (permutation i).symm) ⟨0,by simp⟩ }

/-- Unconditional one-rewrite-per-side matching for the two distinct original
inputs, with an actual residual and no assumed order-exchange law. -/
theorem diagram (copyable : Copyable H) (free : FocusFree H) (positive : 0 < i.val) :
    Rewrite (CopyRule.before T H) (.input ⟨0,by simp⟩)
      (leftAfter T H i) (.input ⟨0,by simp⟩) ∧
    Rewrite (CopyingSelectedInput.after T H i) (.input ⟨0,by simp⟩)
      (rightAfter T H i) (.input ⟨0,by simp⟩) ∧
    Nonempty (CopyingTemplate.Residual (leftAfter T H i) (.input ⟨0,by simp⟩)
      (rightAfter T H i) (.input ⟨0,by simp⟩)) :=
  ⟨left_rewrite T H i copyable,right_rewrite T H i copyable positive,⟨residual T H i copyable free⟩⟩

end Hypernets.Copying.CopyingSelectedInput.OtherZero
