import Hypernets.Copying.RightBareApplicationCut
import Hypernets.Copying.ParametricityLargeBareApplication

/-! The bare larger-right predecessor is exactly the original larger closed
lambda and untouched family, exposing the original callback argument wire. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeRightBare
open Graph Opening
variable {m n} (d : Nat)

noncomputable def remaining : Occurrence (rightFamily d m n)
    (LargeBareApplication.rightAfter (m := m) (n := n) d) :=
  (((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp
      (BareApplyFirst.family (IsolatedFamily.smallRightFamily d m n))).comp
        (BareCall.firstBlock (IsolatedFamily.smallRightFamily d m n) (callback (d+2)))

theorem apart : ∀ e a, (LargeBareApplication.rightBody (m := m) (n := n) d).edges e ≠
    (remaining (m := m) (n := n) d).edges a := by
  intro e a eq
  change (BareCall.bodyOccurrence (hasPrivate := false) (IsolatedFamily.smallRightFamily d m n) (smallRight (d+1)) (callback (d+2))
    (LargeFamilyApplication.rightMember (m := m) (n := n) d)
    (LargeFamilyApplication.right_member_input (m := m) (n := n) d)).edges
      ((LargeOpening.one_bodyIso (d := d)).edges.toFun e) = _ at eq
  generalize (LargeOpening.one_bodyIso (d := d)).edges.toFun e = x at eq
  obtain ⟨part,x⟩ := x
  cases part
  · cases eq
  · obtain ⟨part,x⟩ := x
    cases part <;> cases eq

theorem remaining_input (i : Fin (m+n)) : (remaining (m := m) (n := n) d).ports (.input ⟨i.val,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  have actual : ((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget
      (show [Wire.term]++List.replicate (m+n) Wire.term = List.replicate ((m+n)+1) Wire.term by simp[List.replicate_succ]) rfl).ports
      (.input ⟨i.val,by simp⟩) = .input ⟨i.val+1,by simp⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1;omega))
  change (BareCall.firstBlock _ _).ports ((BareApplyFirst.family _).ports
    (((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).reboundaryTarget _ _).ports (.input ⟨i.val,by simp⟩))) = _
  rw [actual,BareApplyFirst.family_succ]
  change BoundarySerial.leftInsert (BareApplyFirst.net (IsolatedFamily.smallRightFamily d m n)) (callback (d+2)) (.input ⟨i.val+1,by simp⟩) = _
  exact Combined.left_input _ _ _

/-- The opened larger body contributes the actual inner app, selected
smaller lambda and callback; the remaining old family covers every other edge. -/
theorem cover (e : (LargeBareApplication.rightAfter (m := m) (n := n) d).Edge) :
    (∃ a, (LargeBareApplication.rightBody (m := m) (n := n) d).edges a=e) ∨
      ∃ b, (remaining (m := m) (n := n) d).edges b=e := by
  let f := BareCall.bodyOccurrence (hasPrivate := false) (IsolatedFamily.smallRightFamily d m n) (smallRight (d+1)) (callback (d+2))
    (LargeFamilyApplication.rightMember (m := m) (n := n) d)
    (LargeFamilyApplication.right_member_input (m := m) (n := n) d)
  have lift (x : (LargeSplice.body (hasPrivate := false) (smallRight (d+1)) (callback (d+2))).Edge) :
      (LargeBareApplication.rightBody (m := m) (n := n) d).edges
        ((LargeOpening.one_bodyIso (d := d)).edges.invFun x) = f.edges x := by
    change f.edges ((LargeOpening.one_bodyIso (d := d)).edges.toFun ((LargeOpening.one_bodyIso (d := d)).edges.invFun x)) = _
    rw [(LargeOpening.one_bodyIso (d := d)).edges.right_inv]
  obtain ⟨part,e⟩ := e
  cases part
  · obtain ⟨part,e⟩ := e
    cases part
    · exact .inl ⟨_,lift ⟨false,e⟩⟩
    · obtain ⟨part,e⟩ := e
      cases part
      · exact .inl ⟨_,lift ⟨true,⟨false,e⟩⟩⟩
      · exact .inr ⟨e,rfl⟩
  · exact .inl ⟨_,lift ⟨true,⟨true,e⟩⟩⟩

/-- Complete original large-right bare source correspondence, fixing all
external family inputs and the original exposed argument wire. -/
noncomputable def iso : DeepIso
    (BareApplyFirst.net (IsolatedFamily.largeRightFamily d m n))
    (LargeBareApplication.rightBefore (m := m) (n := n) d) := by
  have actual := RightBareApplicationCut.iso rfl (callOneBody d) (rightFamily d m n)
    (LargeBareApplication.rightBody (m := m) (n := n) d) (remaining (m := m) (n := n) d)
    (apart d) (LargeBareApplication.right_input d) (remaining_input d) (LargeBareApplication.right_argument d) (cover d)
  change DeepIso ((BareApplyFirst.net (IsolatedFamily.largeRightFamily d m n)).reboundary rfl rfl)
    (LargeBareApplication.rightBefore (m := m) (n := n) d) at actual
  simpa only [Net.reboundary_refl] using actual

end Hypernets.Copying.Parametricity.LargeRightBare
