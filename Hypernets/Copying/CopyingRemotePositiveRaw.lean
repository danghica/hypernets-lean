import Hypernets.Copying.CopyingRemotePositive
import Hypernets.Copying.CopyingResidualBoundary

/-! The positive-input remote diagram on the literal graft interfaces,
without an arithmetic interface cast at its public endpoints. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRemote.Positive
open Graph Combined ContractionTree
variable {d m n k h : Nat}
    (P : ContractionTree .term (m+1)) (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h)) (j : Fin (n+2))

/-- Actual matched original grafts at their unchanged interface admit one
copy per side and a genuine copying residual at the same upstream input. -/
theorem raw_diagram (copyable : Copyable H) (free : FocusFree H) (positive : 0 < j.val) :
    ∃ X Y : Hypernet d (List.replicate ((m+1)+(n+1)) .term) (environmentInterface k h),
      Rewrite (Graft.net (P.atDepth d) (CopyRule.before T H) j) (.input ⟨0,by simp; omega⟩)
        X (.input ⟨0,by simp; omega⟩) ∧
      Rewrite (Graft.net (P.atDepth d) (CopyRule.after T H) j) (.input ⟨0,by simp; omega⟩)
        Y (.input ⟨0,by simp; omega⟩) ∧
      Nonempty (CopyingTemplate.Residual X (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩)) := by
  let hi : List.replicate ((m+1)+(n+1)) Wire.term = List.replicate (m+n+2) Wire.term := by congr 1; omega
  have l := rewrite_reboundary hi.symm rfl (left_rewrite P T H j copyable)
  have r := rewrite_reboundary hi.symm rfl (right_rewrite P T H j copyable positive)
  have p := (residual P T H j copyable free).reboundary hi.symm rfl
  have leftCancel : (left P T H j).reboundary hi.symm rfl = Graft.net (P.atDepth d) (CopyRule.before T H) j :=
    CopyingTemplate.reboundary_cancel _ hi rfl
  have rightCancel : (right P T H j).reboundary hi.symm rfl = Graft.net (P.atDepth d) (CopyRule.after T H) j :=
    CopyingTemplate.reboundary_cancel _ hi rfl
  simp only [Port.cast] at l r p
  rw [leftCancel] at l
  rw [rightCancel] at r
  exact ⟨_,_,l,r,⟨p⟩⟩

end Hypernets.Copying.CopyingRemote.Positive
