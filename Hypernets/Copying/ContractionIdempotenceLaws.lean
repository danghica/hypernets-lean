import Hypernets.Copying.ContractionIdempotence
import Hypernets.Copying.NullaryTemplates
import Hypernets.Copying.FillingPadding

/-! Structural admissibility and padding for the original Idem template.
Input safety follows from its empty interface, not from a simulation premise. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionIdempotence
open Graph

theorem template_noInputs : template.NoInputs := fun pair => pair.input

theorem template_noTermInputs : template.NoTermInputs := template_noInputs.noTermInputs

theorem template_outputClosed : template.OutputClosed := template_noInputs.outputClosed

/-- Every quantitative input-safety instance is vacuous because a token cannot
enter a fragment with no source ports. The surrounding contexts are arbitrary. -/
theorem template_inputSafe (Allowed : ∀ d, Hypernet d [.term] [] → Prop)
    (Q P : CostOrder) :
    (Specimens.system template Allowed template_outputClosed).InputSafe Q P :=
  template_noInputs.inputSafe Allowed Q P

/-- Padding retains the two separate weakening edges, their ordered junctions,
and the contraction; only graph carrier representation may differ. -/
noncomputable def left_raise (d : Nat) (s : ShareSort) :
    DeepIso (Copying.raise d (left d s)) (left (d+1) s) := by
  unfold left
  simpa only [Padding.tensor,Padding.primitive] using
    Padding.serial (Net.Tensor.net (primitiveNet d (.weakening s))
      (primitiveNet d (.weakening s))) (primitiveNet d (.contraction s))

/-- The single weakening is unchanged by an additional representation allowance. -/
theorem right_raise (d : Nat) (s : ShareSort) :
    Copying.raise d (right d s) = right (d+1) s := Padding.primitive d _

/-- A padded literal pair is still the literal pair up to its ordered graph
representation, with no conversion to an ordinary compute transition. -/
theorem Step.raise {d I O} {G H : Hypernet d I O} (step : Step G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases step with
  | idem s =>
    exact .witness (left_raise _ s) (.idem _ s)
      (by rw [right_raise]; exact DeepIso.refl _)

theorem UpToIso.raise {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f step g =>
    cases step.raise with
    | witness l step r =>
      exact .witness ((Padding.congr f).trans l) step (r.trans (Padding.congr g))

theorem template_paddingClosed : template.PaddingClosed := @UpToIso.raise

end Hypernets.Copying.ContractionIdempotence
