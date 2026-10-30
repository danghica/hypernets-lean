import Hypernets.Copying.ParametricityApplyOccurrence
import Hypernets.Copying.ParametricityIsolatedFamily
import Hypernets.Copying.ParametricityLargeOpening
import Hypernets.Copying.ParametricityPointedCut
import Hypernets.Copying.CompleteMatchExecution

/-! The larger abstractions open in one original beta step each. Their
unevaluated callbacks remain common context around a genuine complete
parametricity specimen for the increased small-abstraction family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeFamilyApplication
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m n O} (d : Nat) (C : ContractionTree .term ((m+n)+1))
    (V : Hypernet (d+2) [.term] O)

/-- The opened left family retains all its remaining original closures,
its original arbitrary sharing tree and its literal private cell. -/
def leftAfter := ApplyFirst.net (IsolatedFamily.smallClosed d C) (LargeOpening.invocation V)
def rightAfter := ApplyFirst.net (IsolatedFamily.smallRightFamily d m n) (LargeOpening.invocation V)

noncomputable def leftMember : Occurrence (smallLeft (d+1)) (IsolatedFamily.smallClosed d C) :=
  (((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m n)).reboundaryTarget _ _).comp
    (BoxPullWeakening.ReverseComponents.serialLeft (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2)))).comp
      (BoxPullWeakening.ReverseComponents.serialLeft
        (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2)))

noncomputable def rightMember : Occurrence (smallRight (d+1)) (IsolatedFamily.smallRightFamily d m n) :=
  (BoxPullWeakening.ReverseComponents.tensorLeft (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget _ _

theorem left_member_input : (leftMember d C).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change BoundarySerial.leftInsert
    (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))
    (BoundarySerial.leftInsert (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2)) (.input ⟨0,by simp⟩)) = _
  rw [left_input,left_input]
theorem right_member_input : (rightMember (m := m) (n := n) d).ports (.input 0) = .input ⟨0,by simp⟩ := rfl

/-- The complete original opened large-left body, including its unchanged
callback and argument, occurs in the actual smaller-family continuation. -/
noncomputable def leftOpened : Occurrence (LargeOpening.readOpened V) (leftAfter d C V) :=
  ApplyFirst.binaryOccurrence (LargeOpening.invocation V) (leftMember d C) (left_member_input d C)

noncomputable def rightOpened : Occurrence (LargeOpening.oneOpened V) (rightAfter (m := m) (n := n) d V) :=
  ApplyFirst.binaryOccurrence (LargeOpening.invocation V) (rightMember (m := m) (n := n) d) (right_member_input (m := m) (n := n) d)

theorem left_opened_input : (leftOpened d C V).ports (.input 0) = .input ⟨0,by simp⟩ :=
  ApplyFirst.binary_input _ _ _
theorem right_opened_input : (rightOpened (m := m) (n := n) d V).ports (.input 0) = .input ⟨0,by simp⟩ :=
  ApplyFirst.binary_input _ _ _

/-- Insert the literal original large beta source in its computed complement. -/
noncomputable def leftBefore := CompleteMatchCut.replaceWith (leftOpened d C V).matchEmbedding
  (leftOpened d C V).label (Application.before (callReadBody d) V)
noncomputable def rightBefore := CompleteMatchCut.replaceWith (rightOpened (m := m) (n := n) d V).matchEmbedding
  (rightOpened (m := m) (n := n) d V).label (Application.before (callOneBody d) V)

/-- The actual left beta rewrite resumes at the original external input. -/
theorem left_beta (stable : Stable V) : Rewrite (leftBefore d C V) (.input ⟨0,by simp⟩)
    (leftAfter d C V) (.input ⟨0,by simp⟩) := by
  have step := CompleteMatchCut.rewrite_into (leftOpened d C V).matchEmbedding (leftOpened d C V).label
    (LargeOpening.read_beta V stable)
  rw [CompleteMatchCut.replace_input _ _ _ _ (left_opened_input d C V)] at step
  change Rewrite (leftBefore d C V) (.input ⟨0,by simp⟩) (leftAfter d C V) ((leftOpened d C V).ports (.input 0)) at step
  rw [left_opened_input] at step
  exact step

/-- The right beta rewrite has the same one-step cost; the callback need not
terminate and is not evaluated by either proof. -/
theorem right_beta (stable : Stable V) : Rewrite (rightBefore (m := m) (n := n) d V) (.input ⟨0,by simp⟩)
    (rightAfter (m := m) (n := n) d V) (.input ⟨0,by simp⟩) := by
  have step := CompleteMatchCut.rewrite_into (rightOpened (m := m) (n := n) d V).matchEmbedding
    (rightOpened (m := m) (n := n) d V).label (LargeOpening.one_beta V stable)
  rw [CompleteMatchCut.replace_input _ _ _ _ (right_opened_input (m := m) (n := n) d V)] at step
  change Rewrite (rightBefore (m := m) (n := n) d V) (.input ⟨0,by simp⟩) (rightAfter (m := m) (n := n) d V) ((rightOpened (m := m) (n := n) d V).ports (.input 0)) at step
  rw [right_opened_input] at step
  exact step

/-- A fully constructed original parametricity filling after the two beta
steps: the smaller abstraction count increases, the larger count decreases,
and the unevaluated callback plus V remains common context. -/
noncomputable def residual (free : FocusFree V) :
    FillingWitness template (leftAfter d C V) (rightAfter (m := m) (n := n) d V) :=
  ApplyFirst.witness _ _ (IsolatedFamily.smallWitness d C)
    (Serial.allLabels_net _ (labels_closed (callback_labels (d+2))).1 free)

noncomputable def pointed (free : FocusFree V) :
    PointedWitness template (leftAfter d C V) (.input ⟨0,by simp⟩)
      (rightAfter (m := m) (n := n) d V) (.input ⟨0,by simp⟩) :=
  .input (residual d C V free) ⟨0,by simp⟩

/-- The complete selected-family large-beta comparison has one genuine
original rewrite on each side and an actual common residual specimen. -/
theorem one_vs_one (stable : Stable V) :
    Rewrite (leftBefore d C V) (.input ⟨0,by simp⟩) (leftAfter d C V) (.input ⟨0,by simp⟩) ∧
    Rewrite (rightBefore (m := m) (n := n) d V) (.input ⟨0,by simp⟩)
      (rightAfter (m := m) (n := n) d V) (.input ⟨0,by simp⟩) ∧
    Nonempty (PointedWitness template (leftAfter d C V) (.input ⟨0,by simp⟩)
      (rightAfter (m := m) (n := n) d V) (.input ⟨0,by simp⟩)) := by
  constructor
  · exact left_beta d C V stable
  constructor
  · exact right_beta (m := m) (n := n) d V stable
  · exact ⟨pointed d C V stable.focusFree⟩

end Hypernets.Copying.Parametricity.LargeFamilyApplication
