import Hypernets.Copying.ParametricityRightApplicationCut
import Hypernets.Copying.ParametricityLargeFamilyApplication

/-! The larger constant-family predecessor is exactly application to the
original larger closed lambda, not merely an unspecified inverse beta cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeRightSource
open Graph Opening
variable {m n O} (d : Nat) (V : Hypernet (d+2) [.term] O)

noncomputable def remaining : Occurrence (rightFamily d m n)
    (LargeFamilyApplication.rightAfter (m := m) (n := n) d V) :=
  ((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp
      (ApplyFirst.family (IsolatedFamily.smallRightFamily d m n) (LargeOpening.invocation V))

theorem apart : ∀ e a, (LargeFamilyApplication.rightOpened (m := m) (n := n) d V).edges e ≠
    (remaining (m := m) (n := n) d V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · cases eq
  · obtain ⟨part,e⟩ := e
    cases part <;> cases eq

theorem remaining_input (i : Fin (m+n)) : (remaining (m := m) (n := n) d V).ports (.input ⟨i.val,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  have actual : ((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget
      (show [Wire.term]++List.replicate (m+n) Wire.term = List.replicate ((m+n)+1) Wire.term by simp[List.replicate_succ]) rfl).ports
      (.input ⟨i.val,by simp⟩) = .input ⟨i.val+1,by simp⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1;omega))
  change (ApplyFirst.family _ _).ports (((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget _ _).ports (.input ⟨i.val,by simp⟩)) = _
  rw [actual,ApplyFirst.family_succ]

theorem body_output (i : Fin O.length) :
    (LargeFamilyApplication.rightOpened (m := m) (n := n) d V).ports (.output i) = .output i := by
  change (ApplyFirst.binaryOccurrence (LargeOpening.invocation V)
    (LargeFamilyApplication.rightMember (m := m) (n := n) d) (LargeFamilyApplication.right_member_input d)).ports (.output i) = _
  rw [ApplyFirst.binaryOccurrence,Occurrence.SerialJoin.occurrence_output]
  let P := ApplyFirst.selected (LargeOpening.invocation V) (LargeFamilyApplication.rightMember (m := m) (n := n) d)
  let A := ApplyFirst.argument (IsolatedFamily.smallRightFamily d m n) (LargeOpening.invocation V)
  have eq := Occurrence.tensorJoin_right P A
    (ApplyFirst.selected_argument_disjoint (LargeOpening.invocation V) (LargeFamilyApplication.rightMember (m := m) (n := n) d)) (.output i)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1))
      (LargeOpening.invocation V)).ports (.output i) = .output i := by
    exact congrArg Port.output (Fin.ext (by change 0+i.val=i.val;simp))
  rw [represented] at eq
  exact eq.trans (ApplyFirst.argument_output _ _ i)

/-- The full opened larger body and unchanged remainder cover exactly the
application, selected smaller closure, callback, argument, and old family. -/
theorem cover (e : (LargeFamilyApplication.rightAfter (m := m) (n := n) d V).Edge) :
    (∃ a, (LargeFamilyApplication.rightOpened (m := m) (n := n) d V).edges a=e) ∨
      ∃ b, (remaining (m := m) (n := n) d V).edges b=e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | none => exact .inl ⟨⟨false,e⟩,rfl⟩
  | some part =>
    cases part
    · obtain ⟨part,e⟩ := e
      cases part
      · exact .inl ⟨⟨true,⟨false,e⟩⟩,rfl⟩
      · exact .inr ⟨e,rfl⟩
    · exact .inl ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Exact original larger-family application source, fixing every external
input and every output of the arbitrary callback argument V. -/
noncomputable def iso : DeepIso
    (ApplyFirst.net (IsolatedFamily.largeRightFamily d m n) V)
    (LargeFamilyApplication.rightBefore (m := m) (n := n) d V) := by
  have actual := RightApplicationCut.iso rfl (rightFamily d m n) (largeRight d) V
    (LargeFamilyApplication.rightOpened (m := m) (n := n) d V) (remaining (m := m) (n := n) d V)
    (apart d V) (LargeFamilyApplication.right_opened_input d V) (remaining_input d V) (body_output d V) (cover d V)
  change DeepIso ((ApplyFirst.net (IsolatedFamily.largeRightFamily d m n) V).reboundary rfl rfl)
    (LargeFamilyApplication.rightBefore (m := m) (n := n) d V) at actual
  simpa only [Net.reboundary_refl] using actual

end Hypernets.Copying.Parametricity.LargeRightSource
