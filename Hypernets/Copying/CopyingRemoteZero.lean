import Hypernets.Copying.CopyingRemoteRightPair
import Hypernets.Copying.CopyingRemoteLeft
import Hypernets.Copying.CopyingMergeAssociativity
import Hypernets.Copying.CopyingMergeRetainedIso
import Hypernets.Copying.CopyingResidualBoundary
import Hypernets.Copying.ContractionTreeGraftRewrite
import Hypernets.Copying.CopyingFillingReverse

/-! The distinguished-input remote copying overlap. One actual original copy
occurs on each side. Their residuals contain one genuine copying instance
between independently proved exact sharing corrections. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRemote.Zero
open Graph Combined ContractionTree
open BoxPullWeakening (PointedWitness)
variable {d m b k h : Nat}
    (P : ContractionTree .term (m+1)) (T : ContractionTree .term (b+1))
    (H : Hypernet d [.term] (environmentInterface k h))

def left : Hypernet d (List.replicate (m+b+1) .term) (environmentInterface k h) :=
  (Graft.net (P.atDepth d) (CopyRule.before T H) 0).reboundary (by congr 1; omega) rfl

def right : Hypernet d (List.replicate (m+b+1) .term) (environmentInterface k h) :=
  (Graft.net (P.atDepth d) (CopyRule.after T H) 0).reboundary (by congr 1; omega) rfl

def rightAfter : Hypernet d (List.replicate (m+b+1) .term) (environmentInterface k h) :=
  (CopyingRemoteRight.after P T H).reboundary (by congr 1; omega) rfl

/-- The right actual successor and the original residual's right endpoint
have the same three payloads. Only the two canonical resource-row
parenthesizations differ, and their equivalence is a genuine sharing filling. -/
noncomputable def trailing (free : FocusFree H) :
    FillingWitness SharingTreeAlgebra.template (Left.middleAfter P T H 0) (rightAfter P T H) := by
  let B := Serial.net (CopyRule.residual P d) H
  let C := Serial.net (CopyRule.residual T d) H
  have bf : FocusFree B := Serial.allLabels_net _
    (CopyRule.residual_allLabels _ P d (by intro mode bad; cases bad) (by intro mode bad; cases bad)) free
  have cf : FocusFree C := Serial.allLabels_net _
    (CopyRule.residual_allLabels _ T d (by intro mode bad; cases bad) (by intro mode bad; cases bad)) free
  have w := (CopyingMerge.assoc (a := 1) H B C free bf cf).reboundary
    (show List.replicate ((1+m)+b) Wire.term = List.replicate (m+b+1) Wire.term by congr 1; omega) rfl
  have lhs := CopyRule.reboundaryIso (CopyingMerge.retainedLeftIso H B C)
    (show List.replicate ((m+1)+b) Wire.term = List.replicate (m+b+1) Wire.term by congr 1; omega) rfl
  have rhs := (CopyingMerge.retainedCongr H
    (CopyingRemoteRight.factorIso (a := m) (CopyRule.residual P d) H C)).trans
      (CopyingMerge.retainedIso H (CopyingMerge.net B C))
  simp only [CopyingMerge.reboundary_comp] at w lhs
  have forward : FillingWitness SharingTreeAlgebra.template (rightAfter P T H) (Left.middleAfter P T H 0) :=
    w.congr lhs.symm rhs.symm
  exact forward.reverseSharing

/-- The left upstream match is the original copying rule on the complete
grafted tree, with the literal original source and input order preserved. -/
theorem left_rewrite (copyable : Copyable H) :
    Rewrite (left P T H) (.input ⟨0,by simp⟩)
      (CopyRule.after (Graft.copyTree P T 0) H) (.input ⟨0,by simp⟩) :=
  (Rewrite.local (.copy (Graft.copyTree P T 0) H copyable)).rename
    (Graft.copy_source_iso P T H 0) (DeepIso.refl _)

/-- The right source admits one actual original upstream copying rewrite,
including the case where the shallow component has no remaining input. -/
theorem right_rewrite (copyable : Copyable H) :
    Rewrite (right P T H) (.input ⟨0,by simp⟩)
      (rightAfter P T H) (.input ⟨0,by simp⟩) := by
  have step := rewrite_reboundary
    (show List.replicate ((m+1)+b) Wire.term = List.replicate (m+b+1) Wire.term by congr 1; omega)
    rfl (CopyingRemoteRight.rewrite P T H copyable)
  exact step

/-- The complete residual has exactly one original copying link, with
actual sharing certificates on both sides and the same ordered resume port. -/
noncomputable def residual (copyable : Copyable H) (free : FocusFree H) :
    CopyingTemplate.TwoSidedResidual
      (CopyRule.after (Graft.copyTree P T 0) H) (.input ⟨0,by simp⟩)
      (rightAfter P T H) (.input ⟨0,by simp⟩) := {
  middle := Left.middleBefore P T H 0
  point := .input ⟨0,by simp⟩
  leading := PointedWitness.input (Left.leading P T H 0 free) ⟨0,by simp⟩
  rest := {
    middle := Left.middleAfter P T H 0
    point := .input ⟨0,by simp⟩
    paired := PointedWitness.input (Left.original P T H 0 copyable free) ⟨0,by simp⟩
    correction := PointedWitness.input (trailing P T H free) ⟨0,by simp⟩ } }

/-- The literal distinguished-input graft diagram has no assumed matching,
residual, or semantic law. Both costs are one rewrite and the residual keeps
the paper's original directed copying template. -/
theorem raw_diagram (copyable : Copyable H) (free : FocusFree H) :
    ∃ X Y : Hypernet d (List.replicate ((m+1)+b) .term) (environmentInterface k h),
      Rewrite (Graft.net (P.atDepth d) (CopyRule.before T H) 0) (.input ⟨0,by simp; omega⟩)
        X (.input ⟨0,by simp; omega⟩) ∧
      Rewrite (Graft.net (P.atDepth d) (CopyRule.after T H) 0) (.input ⟨0,by simp; omega⟩)
        Y (.input ⟨0,by simp; omega⟩) ∧
      Nonempty (CopyingTemplate.TwoSidedResidual X (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩)) := by
  let hi : List.replicate ((m+1)+b) Wire.term = List.replicate (m+b+1) Wire.term := by congr 1; omega
  have l := rewrite_reboundary hi.symm rfl (left_rewrite P T H copyable)
  have r := rewrite_reboundary hi.symm rfl (right_rewrite P T H copyable)
  have p := (residual P T H copyable free).reboundary hi.symm rfl
  have leftCancel : (left P T H).reboundary hi.symm rfl = Graft.net (P.atDepth d) (CopyRule.before T H) 0 :=
    CopyingTemplate.reboundary_cancel _ hi rfl
  have rightCancel : (right P T H).reboundary hi.symm rfl = Graft.net (P.atDepth d) (CopyRule.after T H) 0 :=
    CopyingTemplate.reboundary_cancel _ hi rfl
  simp only [Port.cast] at l r p
  rw [leftCancel] at l
  rw [rightCancel] at r
  exact ⟨_,_,l,r,⟨p⟩⟩

end Hypernets.Copying.CopyingRemote.Zero
