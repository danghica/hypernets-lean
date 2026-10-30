import Hypernets.Copying.CopyingTemplate
import Hypernets.Copying.FillingPadding

/-! Output closure and representation padding for the literal copying
pre-template, retaining its complete multi-input shape. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph

/-- A distributor contains only sharing labels. Hence no operation-only
path can arrive at any of its output wires. -/
theorem distributor_oneWay (d k h m : Nat) :
    OneWay (Translation.environmentDistributor d k h m) := by
  let D := Translation.environmentDistributor d k h m
  have labels : AllLabels (fun p => ∀ o, p ≠ .operation o) D :=
    Translation.allLabels_tensor _
      (Distributor.allLabels_atDepth _ .term k m d
        (by intro o eq; cases eq) (by intro o eq; cases eq))
      (Distributor.allLabels_atDepth _ .atom h m d
        (by intro o eq; cases eq) (by intro o eq; cases eq))
  intro j _ reach
  obtain ⟨e,target⟩ := (D.target_coverage (.output j)).mpr (by simp [Port.IsInput])
  apply reach.not_nonoperation_target _ target
  intro o eq
  have bad := labels e
  rw [eq] at bad
  cases d <;> exact bad o rfl

/-- The literal right side is one-way because its final term and atom
distributors intercept all its outputs, regardless of the payload body. -/
theorem Literal.outputClosed {d I O} {G H : Hypernet d I O} (pair : Literal G H) :
    OneWay H := by
  cases pair with
  | copy tree H copyable free =>
    exact OneWay.serial_right (CopyRule.copies tree H) _ (distributor_oneWay _ _ _ _)

theorem Pair.outputClosed {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    OneWay H := by
  cases pair with
  | witness _ p g => exact (OneWay.iso_iff g).mp p.outputClosed

theorem template_outputClosed : template.OutputClosed := fun pair => .inr pair.outputClosed

/-- Raising the allowance preserves the same tree and raises the original
payload recursively; both sides remain the original copying construction. -/
theorem Literal.raise {d I O} {G H : Hypernet d I O} (pair : Literal G H) :
    Pair (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | copy tree H copyable free =>
    exact .witness (CopyRule.before_raise tree H)
      (.copy tree _ copyable.raise ((allLabels_raise_iff _ _ _).mpr free))
      (CopyRule.after_raise tree H).symm

theorem Pair.raise {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    Pair (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f p g =>
    cases p.raise with
    | witness l p r =>
      exact .witness ((Padding.congr f).trans l) p (r.trans (Padding.congr g))

theorem template_paddingClosed : template.PaddingClosed := @Pair.raise

end Hypernets.Copying.CopyingTemplate
