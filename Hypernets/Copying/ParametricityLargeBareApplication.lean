import Hypernets.Copying.ParametricityBareCall
import Hypernets.Copying.ParametricityLargeFamilyApplication
import Hypernets.Copying.OpeningCertificateInverseCut

/-! The larger family beta diagram exposes the actual argument wire.
No argument edge is cut out of its owning original template component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeBareApplication
open Graph Opening Combined Application
open BoxPullWeakening (PointedWitness)
variable {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1))

/-- The callback remains an unevaluated serial suffix; its free output is
the original argument wire, with no value graph included in this footprint. -/
def leftAfter := Serial.net (BareApplyFirst.net (IsolatedFamily.smallClosed d C)) (callback (d+2))
def rightAfter := Serial.net (BareApplyFirst.net (IsolatedFamily.smallRightFamily d m n)) (callback (d+2))

noncomputable def leftBody : Occurrence (openBody (callReadBody d)) (leftAfter d C) :=
  (Occurrence.ofIso (LargeOpening.read_bodyIso (d := d))).comp
    (BareCall.bodyOccurrence (hasPrivate := true) (IsolatedFamily.smallClosed d C) (smallLeft (d+1)) (callback (d+2))
      (LargeFamilyApplication.leftMember d C) (LargeFamilyApplication.left_member_input d C))
noncomputable def rightBody : Occurrence (openBody (callOneBody d)) (rightAfter (m := m) (n := n) d) :=
  (Occurrence.ofIso (LargeOpening.one_bodyIso (d := d))).comp
    (BareCall.bodyOccurrence (hasPrivate := false) (IsolatedFamily.smallRightFamily d m n) (smallRight (d+1)) (callback (d+2))
      (LargeFamilyApplication.rightMember (m := m) (n := n) d)
      (LargeFamilyApplication.right_member_input (m := m) (n := n) d))

theorem left_input : (leftBody d C).ports (.input 0) = .input ⟨0,by simp⟩ :=
  BareCall.body_input (hasPrivate := true) (IsolatedFamily.smallClosed d C) (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C) (LargeFamilyApplication.left_member_input d C)
theorem right_input : (rightBody (m := m) (n := n) d).ports (.input 0) = .input ⟨0,by simp⟩ :=
  BareCall.body_input (hasPrivate := false) (IsolatedFamily.smallRightFamily d m n) (smallRight (d+1)) (callback (d+2)) (LargeFamilyApplication.rightMember (m := m) (n := n) d) (LargeFamilyApplication.right_member_input (m := m) (n := n) d)
theorem left_argument : (leftBody d C).ports (.output 0) = .output 0 :=
  BareCall.body_argument (hasPrivate := true) (IsolatedFamily.smallClosed d C) (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C) (LargeFamilyApplication.left_member_input d C)
theorem right_argument : (rightBody (m := m) (n := n) d).ports (.output 0) = .output 0 :=
  BareCall.body_argument (hasPrivate := false) (IsolatedFamily.smallRightFamily d m n) (smallRight (d+1)) (callback (d+2)) (LargeFamilyApplication.rightMember (m := m) (n := n) d) (LargeFamilyApplication.right_member_input (m := m) (n := n) d)

noncomputable def leftBefore := CompleteMatchCut.replaceWith (leftBody d C).matchEmbedding
  (leftBody d C).label (RetainedFrame.net (callReadBody d))
noncomputable def rightBefore := CompleteMatchCut.replaceWith (rightBody (m := m) (n := n) d).matchEmbedding
  (rightBody (m := m) (n := n) d).label (RetainedFrame.net (callOneBody d))

/-- These are complete source-relative geometric opening certificates.
Actual beta in the running host is enabled separately by original rootedness. -/
noncomputable def left_certificate : OpeningCertificate (leftBefore d C) (leftAfter d C)
    (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) (callReadBody d) := by
  have cert := (leftBody d C).opening_into (RetainedFrame.certificate (callReadBody d))
  rw [CompleteMatchCut.replace_input _ _ _ _ (left_input d C),left_input] at cert
  exact cert
noncomputable def right_certificate : OpeningCertificate
    (rightBefore (m := m) (n := n) d) (rightAfter (m := m) (n := n) d)
    (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) (callOneBody d) := by
  have cert := (rightBody (m := m) (n := n) d).opening_into (RetainedFrame.certificate (callOneBody d))
  rw [CompleteMatchCut.replace_input _ _ _ _ (right_input (m := m) (n := n) d),right_input] at cert
  exact cert

/-- Opening replaces the selected large member by a small member and keeps
the full original callback in a common graph context. -/
noncomputable def residual : FillingWitness template (leftAfter d C) (rightAfter (m := m) (n := n) d) :=
  (BareApplyFirst.witness (IsolatedFamily.smallClosed d C) (IsolatedFamily.smallWitness d C)).serial
    (FillingWitness.refl (callback (d+2)) (labels_closed (callback_labels (d+2))).1)

noncomputable def pointed : PointedWitness template (leftAfter d C) (.input ⟨0,by simp⟩)
    (rightAfter (m := m) (n := n) d) (.input ⟨0,by simp⟩) :=
  .input (residual d C) ⟨0,by simp⟩

end Hypernets.Copying.Parametricity.LargeBareApplication
