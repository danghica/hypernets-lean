import Hypernets.Copying.ParametricityRightApplicationCut
import Hypernets.Copying.ParametricitySmallFamilyApplication
import Hypernets.Copying.ParametricityIsolatedFamily

/-! Exact source correspondence for the smaller constant-returning family's
original beta predecessor, including all remaining closures and V outputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallRightSource
open Graph Opening
variable {m n O} (d : Nat) (V : Hypernet (d+2) [.term] O)

noncomputable def remaining : Occurrence (rightFamily d m n)
    (SmallFamilyApplication.counterpart (m₁ := m) (m₂ := n) d V) :=
  ((BoxPullWeakening.ReverseComponents.tensorRight (ReadTail.numeral (d+2)) (rightFamily d m n)).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp
      (CompleteMatchCut.TensorLeft.selected (SmallFamilyRead.counterpart (m₁ := m) (m₂ := n) d)
        (SmallFamilyApplication.discarded d V))

theorem apart : ∀ e a, (SmallFamilyApplication.rightBody (m₁ := m) (m₂ := n) d V).edges e ≠
    (remaining (m := m) (n := n) d V).edges a := by
  rintro ⟨part,e⟩ a eq; cases part <;> cases eq

theorem remaining_input (i : Fin (m+n)) : (remaining (m := m) (n := n) d V).ports (.input ⟨i.val,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1;omega))

theorem body_output (i : Fin O.length) :
    (SmallFamilyApplication.rightBody (m₁ := m) (m₂ := n) d V).ports (.output i) = .output i := by
  let P := SmallFamilyApplication.numeralOccurrence (m₁ := m) (m₂ := n) d V
  let A := SmallFamilyApplication.rightArgument (m₁ := m) (m₂ := n) d V
  have eq := Occurrence.tensorJoin_right P A (SmallFamilyApplication.right_disjoint (m₁ := m) (m₂ := n) d V) (.output i)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (ReadTail.numeral (d+2))
      (SmallFamilyApplication.discarded d V)).ports (.output i) = .output i := by
    exact congrArg Port.output (Fin.ext (by change 0+i.val=i.val;simp))
  rw [represented] at eq
  change (SmallFamilyApplication.rightBody (m₁ := m) (m₂ := n) d V).ports (.output i) = A.ports (.output i) at eq
  refine eq.trans ?_
  exact congrArg Port.output (Fin.ext (by change 0+i.val=i.val;simp))

/-- The local constant/discarded-argument reduct and unchanged remaining
family partition every original edge. -/
theorem cover (e : (SmallFamilyApplication.counterpart (m₁ := m) (m₂ := n) d V).Edge) :
    (∃ a, (SmallFamilyApplication.rightBody (m₁ := m) (m₂ := n) d V).edges a=e) ∨
      ∃ b, (remaining (m := m) (n := n) d V).edges b=e := by
  obtain ⟨part,e⟩ := e
  cases part
  · obtain ⟨part,e⟩ := e
    cases part
    · exact .inl ⟨⟨false,e⟩,rfl⟩
    · exact .inr ⟨e,rfl⟩
  · exact .inl ⟨⟨true,e⟩,rfl⟩

/-- The computed predecessor is exactly application to the original isolated
small-right family, with the original ordered argument resources. -/
noncomputable def iso : DeepIso
    ((ApplyFirst.net (IsolatedFamily.smallRightFamily d m n) V).reboundary (List.append_nil _).symm rfl)
    (SmallFamilyApplication.rightBefore (m₁ := m) (m₂ := n) d V) :=
  RightApplicationCut.iso (List.append_nil _) (rightFamily d m n) (smallRight (d+1)) V
    (SmallFamilyApplication.rightBody (m₁ := m) (m₂ := n) d V) (remaining (m := m) (n := n) d V)
    (apart d V) (SmallFamilyApplication.rightBody_input d V) (remaining_input d V) (body_output d V) (cover d V)

end Hypernets.Copying.Parametricity.SmallRightSource
