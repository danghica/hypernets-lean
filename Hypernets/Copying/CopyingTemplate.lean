import Hypernets.Copying.OperationalTemplates
import Hypernets.Copying.CopySafety
import Hypernets.Copying.CopyTransport

/-! The copying pre-template is the token-erasure of the original Figure 17
rule. The entire ordered input interface and the residual contraction tree
are retained, including the selected input's new weakening. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph

/-- Figure 17 without its token: an arbitrary term contraction tree and the
original copyable payload, with the two actual output distributors. -/
inductive Literal : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | copy {d n k h} (tree : ContractionTree .term (n+1))
      (H : Hypernet d [.term] (environmentInterface k h))
      (copyable : Copyable H) (free : FocusFree H) :
      Literal (CopyRule.before tree H) (CopyRule.after tree H)

/-- Each side may use its own graph carrier while preserving all ordered
external ports and every recursive box body. -/
inductive Pair : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (literal : Literal A B) (right : DeepIso B H) : Pair G H

theorem Literal.focusFree {d I O} {G H : Hypernet d I O} (pair : Literal G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | copy tree H copyable free =>
    exact ⟨CopyRule.before_allLabels _ tree H free
      (by intro m eq; cases eq) (by intro m eq; cases eq),
      CopyRule.focusFree_after tree H free⟩

theorem Pair.focusFree {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f p g => exact ⟨(allLabels_iso_iff _ f).mpr p.focusFree.1,
      (allLabels_iso_iff _ g).mp p.focusFree.2⟩

/-- This pre-template has no assumed simulation, robustness, or contextual
equivalence; its relation is precisely the original copying graphs. -/
def template : PreTemplate where
  Rel := Pair
  focus_free pair := pair.focusFree

theorem literal {d n k h} (tree : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (copyable : Copyable H) (free : FocusFree H) :
    template.Rel (CopyRule.before tree H) (CopyRule.after tree H) :=
  .witness (DeepIso.refl _) (.copy tree H copyable free) (DeepIso.refl _)

/-- The token-erased rule retains every input, not only the distinguished
input at which its compute step is specified. -/
theorem Literal.inputs {d I O} {G H : Hypernet d I O} (pair : Literal G H) :
    ∃ n, I = List.replicate (n+1) .term := by
  cases pair
  exact ⟨_,rfl⟩

theorem Pair.inputs {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    ∃ n, I = List.replicate (n+1) .term := by
  cases pair with
  | witness _ p _ => exact p.inputs

end Hypernets.Copying.CopyingTemplate
