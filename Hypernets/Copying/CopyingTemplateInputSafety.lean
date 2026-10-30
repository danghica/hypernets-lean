import Hypernets.Copying.CopyingDoubleInterchange
import Hypernets.Copying.CopyingDoubleAtResidual
import Hypernets.Copying.CopyingTemplateInputAssembly

/-! Unconditional input safety of the original unrestricted copying template.
The distinguished input consumes the literal copy in two transitions. Every
other ordered input uses two actual copy prefixes and the proved two-copy
sharing interchange, retaining all original payloads and residual trees. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined

/-- Each non-distinguished input of the literal family has its actual 2/2
entry diamond and an original copying residual corrected by sharing alone. -/
theorem Literal.other_entry {d I O} {G H : Hypernet d I O}
    (pair : Literal G H) (i : Fin I.length) (positive : 0 < i.val) :
    ∃ A B : Hypernet d I O,
      Search.Step G (.search,.input i) (.rewrite,.input i) ∧
      Search.Step H (.search,.input i) (.rewrite,.input i) ∧
      Rewrite G (.input i) A (.input i) ∧ Rewrite H (.input i) B (.input i) ∧
      Nonempty (Residual A (.input i) B (.input i)) := by
  cases pair with
  | @copy n k h tree A copyable free =>
    cases n with
    | zero =>
      have bound := i.isLt
      simp only [List.length_replicate] at bound
      omega
    | succ n =>
      refine ⟨CopyingDoubleAt.leftAfter tree A i,CopyingDoubleAt.rightAfter tree A i,
        requests_copy tree A i,CopyingDoubleAt.right_request tree A i copyable positive,
        CopyingDoubleAt.left_rewrite tree A i copyable,
        CopyingDoubleAt.right_rewrite tree A i copyable positive,?_⟩
      exact ⟨CopyingDoubleAt.residual tree A i copyable free
        (CopyingDouble.interchange (CopyingDoubleAt.normalized tree i) A free)⟩

/-- Independent representations of both endpoints preserve the literal local
entry diagrams. No determinism, residual, or semantic premise remains. -/
theorem otherEntries : OtherEntries := by
  intro d I O G H pair i positive
  cases pair with
  | witness f literal g =>
    obtain ⟨A,B,lq,rq,ls,rs,residual⟩ := literal.other_entry i positive
    refine ⟨A,B,?_,?_,?_,?_,residual⟩
    · exact (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).step lq
    · exact (Search.ofBoundaryIso (BoundaryIso.ofDeepIso g)).step rq
    · exact ls.rename f.symm (DeepIso.refl A)
    · exact rs.rename g (DeepIso.refl B)

/-- Original copying is input safe in every focus-free surrounding context
for every cost comparison permitting its exact distinguished 2/0 prefix. -/
theorem template_inputSafe_cost (Q P : CostOrder) (selectedCost : Q.rel 2 0) :
    (Specimens.system template Specimens.allContexts template_outputClosed).InputSafe Q P :=
  inputSafe_of_otherEntries otherEntries Q P selectedCost

/-- Forgetting costs gives unrestricted copying input safety directly. -/
theorem template_inputSafe (P : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).InputSafe CostOrder.any P :=
  template_inputSafe_cost CostOrder.any P trivial

/-- The paper's quantitative input-safety comparison retains the original
left-to-right improvement rather than erasing the distinguished copying cost. -/
theorem template_inputSafe_improvement (P : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).InputSafe CostOrder.improvement P :=
  template_inputSafe_cost CostOrder.improvement P (Nat.zero_le 2)

end Hypernets.Copying.CopyingTemplate
