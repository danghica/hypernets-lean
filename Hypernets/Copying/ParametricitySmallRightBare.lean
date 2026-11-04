import Hypernets.Copying.RightBareApplicationCut
import Hypernets.Copying.ParametricitySmallBareApplication
import Hypernets.Copying.ParametricityIsolatedFamily

/-! The bare smaller-right predecessor is exactly the original isolated
constant-returning family application, with no argument graph captured. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallRightBare
open Graph Opening
variable {m n} (d : Nat)

noncomputable def remaining : Occurrence (rightFamily d m n)
    (SmallBareApplication.counterpart (m₁ := m) (m₂ := n) d) :=
  ((BoxPullWeakening.ReverseComponents.tensorRight (ReadTail.numeral (d+2)) (rightFamily d m n)).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp
      (CompleteMatchCut.TensorLeft.selected (SmallFamilyRead.counterpart (m₁ := m) (m₂ := n) d)
        (SmallBareApplication.weak d))

theorem apart : ∀ e a, (SmallBareApplication.rightBody (m₁ := m) (m₂ := n) d).edges e ≠
    (remaining (m := m) (n := n) d).edges a := by
  intro e a eq
  change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (B := []) (ReadTail.numeral (d+2)) .term
    (SmallBareApplication.numeralOccurrence (m₁ := m) (m₂ := n) d)
    (SmallBareApplication.rightWeakening (m₁ := m) (m₂ := n) d)
    (SmallBareApplication.right_disjoint (m₁ := m) (m₂ := n) d)).edges
      ((SmallBareApplication.rightBodyIso d).edges.toFun e) = _ at eq
  generalize (SmallBareApplication.rightBodyIso d).edges.toFun e = x at eq
  obtain ⟨part,x⟩ := x
  cases part <;> cases eq

theorem remaining_input (i : Fin (m+n)) : (remaining (m := m) (n := n) d).ports (.input ⟨i.val,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1;omega))

/-- The original opened numeral/weakening body and untouched family cover
all actual reduct edges, including the canonical unused binder weakening. -/
theorem cover (e : (SmallBareApplication.counterpart (m₁ := m) (m₂ := n) d).Edge) :
    (∃ a, (SmallBareApplication.rightBody (m₁ := m) (m₂ := n) d).edges a=e) ∨
      ∃ b, (remaining (m := m) (n := n) d).edges b=e := by
  obtain ⟨part,e⟩ := e
  cases part
  · obtain ⟨part,e⟩ := e
    cases part
    · refine .inl ⟨(SmallBareApplication.rightBodyIso d).edges.invFun ⟨false,e⟩,?_⟩
      change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (B := []) (ReadTail.numeral (d+2)) .term
        (SmallBareApplication.numeralOccurrence (m₁ := m) (m₂ := n) d)
        (SmallBareApplication.rightWeakening (m₁ := m) (m₂ := n) d)
        (SmallBareApplication.right_disjoint (m₁ := m) (m₂ := n) d)).edges
          ((SmallBareApplication.rightBodyIso d).edges.toFun ((SmallBareApplication.rightBodyIso d).edges.invFun _)) = _
      rw [(SmallBareApplication.rightBodyIso d).edges.right_inv]
      rfl
    · exact .inr ⟨e,rfl⟩
  · refine .inl ⟨(SmallBareApplication.rightBodyIso d).edges.invFun ⟨true,e⟩,?_⟩
    change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (B := []) (ReadTail.numeral (d+2)) .term
      (SmallBareApplication.numeralOccurrence (m₁ := m) (m₂ := n) d)
      (SmallBareApplication.rightWeakening (m₁ := m) (m₂ := n) d)
      (SmallBareApplication.right_disjoint (m₁ := m) (m₂ := n) d)).edges
        ((SmallBareApplication.rightBodyIso d).edges.toFun ((SmallBareApplication.rightBodyIso d).edges.invFun _)) = _
    rw [(SmallBareApplication.rightBodyIso d).edges.right_inv]
    rfl

/-- Exact original bare application source, at all family arities including
an empty remaining family. The sole output is the untouched argument wire. -/
noncomputable def iso : DeepIso
    ((BareApplyFirst.net (IsolatedFamily.smallRightFamily d m n)).reboundary (List.append_nil _).symm rfl)
    (SmallBareApplication.rightBefore (m₁ := m) (m₂ := n) d) :=
  RightBareApplicationCut.iso (List.append_nil _) (oneBody (d+1)) (rightFamily d m n)
    (SmallBareApplication.rightBody (m₁ := m) (m₂ := n) d) (remaining (m := m) (n := n) d)
    (apart d) (SmallBareApplication.rightBody_input d) (remaining_input d) (SmallBareApplication.rightBody_bound d) (cover d)

end Hypernets.Copying.Parametricity.SmallRightBare
