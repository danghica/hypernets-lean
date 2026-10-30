import Hypernets.Copying.GarbageCollection
import Hypernets.Copying.FillingPadding

/-! Structural safety and padding of the literal garbage-collection family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.GarbageCollection
open Graph

theorem template_noInputs : template.NoInputs := fun pair => pair.input

theorem template_outputClosed : template.OutputClosed := template_noInputs.outputClosed

/-- Input safety holds for every context class and both cost parameters. -/
theorem template_inputSafe (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (Q P : CostOrder) :
    (Specimens.system template Allowed template_outputClosed).InputSafe Q P :=
  template_noInputs.inputSafe Allowed Q P

/-- Padding preserves the actual arbitrary zero-input contraction tree. -/
theorem tree_raise (tree : ContractionTree .term 0) (d : Nat) :
    Copying.raise d (tree.atDepth d) = tree.atDepth (d+1) := by
  cases d <;> rfl

/-- Padding retains the tree and raises the original payload, including its
box bodies, up to the serial constructor's ordered carrier representation. -/
noncomputable def left_raise {d k h} (tree : ContractionTree .term 0)
    (H : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (Copying.raise d (left tree H)) (left tree (Copying.raise d H)) := by
  simpa only [left,tree_raise] using Padding.serial (tree.atDepth d) H

/-- The same two zero-use distributors remain on the right at the next allowance. -/
theorem right_raise (d k h : Nat) :
    Copying.raise d (right d k h) = right (d+1) k h := by
  unfold right
  rw [Padding.castInterfaces,Padding.environmentDistributor]

theorem Step.raise {d I O} {G H : Hypernet d I O} (step : Step G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases step with
  | collect tree H copyable free =>
    exact .witness (left_raise tree H)
      (.collect tree _ copyable.raise ((allLabels_raise_iff _ _ _).mpr free))
      (by rw [right_raise]; exact DeepIso.refl _)

theorem UpToIso.raise {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f step g =>
    cases step.raise with
    | witness l step r =>
      exact .witness ((Padding.congr f).trans l) step (r.trans (Padding.congr g))

theorem template_paddingClosed : template.PaddingClosed := @UpToIso.raise

end Hypernets.Copying.GarbageCollection
