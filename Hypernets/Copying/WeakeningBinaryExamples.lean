import Hypernets.Copying.WeakeningPadding

/-! Checked instances with independent operands, mixed environments, effects,
and different box depths. These are graph weakening calculations, not claims
that the still-open atomic translation weakening cases have been proved. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Examples
open Graph BoxPullWeakening

/-- An open callback body uses its argument and an existing atom. -/
def callbackBody : Hypernet 0 [.term] (environmentInterface 3 2) :=
  Translation.term (.app (.var 0) (.unary .deref (.atom 1)) : Term 3 2)

/-- An independent literal retains the same two-variable, two-atom context. -/
def allocationValue : Hypernet 0 [.term] (environmentInterface 2 2) :=
  Translation.term (.const (.nat 1) : Term 2 2)

/-- Allocation and a separately translated closure can be assigned at their
actual common depth. The source contains a BPullW body and an independent
unary Idem calculation; the target is the original whole translation. -/
noncomputable def assignment_closure (s : ShareSort) :
    Calculation
      (Translation.binary .assign
        (Translation.padTo 1 (by decide) (Translation.unary .ref (extend allocationValue s)))
        (Translation.padTo 1 (by decide) (Translation.abstraction (betaBody callbackBody s))))
      (extend (Translation.term
        (.binary .assign (.unary .ref (.const (.nat 1)))
          (.lam (.app (.var 0) (.unary .deref (.atom 1)))) : Term 2 2)) s) :=
  binary_step_padded .assign s
    (unary_extend .ref allocationValue s (Translation.term_focusFree _))
    (abstraction_extend callbackBody s (Translation.term_focusFree _))

/-- The untouched abstraction operand already contains an inner lambda box. -/
def nestedCallbackBody : Hypernet 1 [.term] (environmentInterface 3 2) :=
  Translation.term (.lam (.app (.var 1) (.var 0)) : Term 3 2)

/-- Independent one-box and two-box operands combine using the original max
padding, with no requirement that their graph carriers or bodies coincide. -/
noncomputable def unequal_depth_application (s : ShareSort) :
    Calculation
      (Translation.application
        (Translation.padTo 2 (by decide) (Translation.abstraction (betaBody nestedCallbackBody s)))
        (Translation.padTo 2 (by decide) (Translation.abstraction (betaBody callbackBody s))))
      (extend (Translation.term
        (.app (.lam (.lam (.app (.var 1) (.var 0))))
          (.lam (.app (.var 0) (.unary .deref (.atom 1)))) : Term 2 2)) s) :=
  application_step_padded s
    (abstraction_extend nestedCallbackBody s (Translation.term_focusFree _))
    (abstraction_extend callbackBody s (Translation.term_focusFree _))

/-- The canonical unused binary component has precisely five edges, for both
sharing sorts and at arbitrary box allowance. The residual has just one. -/
theorem removed_row_size (d : Nat) (s : ShareSort) :
    (IdemRow.canonical d s).finiteEdge.elements.length = 5 ∧
    (primitiveNet d (.weakening s)).finiteEdge.elements.length = 1 := by
  cases d <;> cases s <;> constructor <;> rfl

end Hypernets.Copying.Weakening.Examples
