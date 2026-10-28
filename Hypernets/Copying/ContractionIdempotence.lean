import Hypernets.Copying.TemplateInputSafety
import Hypernets.Copying.TranslationClauses

/-! The literal Idem pair in Figure 21. Two weakenings feeding a contraction
are compared with one weakening, for either the term or atom wire sort.
These are graph constructors and structural template laws, not assumed
observational equivalences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionIdempotence
open Graph

/-- The original three-edge left side: two separate weakenings feed the two
ordered inputs of a contraction. Its sole output has the selected sharing sort. -/
def left (d : Nat) (s : ShareSort) : Hypernet d [] [s.wire] :=
  Serial.net (Net.Tensor.net (primitiveNet d (.weakening s))
    (primitiveNet d (.weakening s))) (primitiveNet d (.contraction s))

/-- The original right side is a single weakening of the same wire sort. -/
def right (d : Nat) (s : ShareSort) : Hypernet d [] [s.wire] :=
  primitiveNet d (.weakening s)

/-- Both literal Figure 21 instances, with no semantic premise. -/
inductive Step : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | idem (d : Nat) (s : ShareSort) : Step (left d s) (right d s)

/-- The graph carriers may be renamed independently on the two sides; each
ordered external interface remains fixed. -/
inductive UpToIso : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (step : Step A B) (right : DeepIso B H) : UpToIso G H

/-- The left graph introduces precisely the two sharing primitives used in
the literal rule; arbitrary restrictions on those primitives propagate. -/
theorem left_allLabels (P : Primitive → Prop) (d : Nat) (s : ShareSort)
    (weakening : P (.weakening s)) (contraction : P (.contraction s)) :
    AllLabels P (left d s) :=
  Serial.allLabels_net P
    (Translation.allLabels_tensor P
      (Translation.allLabels_primitive P d _ weakening)
      (Translation.allLabels_primitive P d _ weakening))
    (Translation.allLabels_primitive P d _ contraction)

/-- The right graph contains only its actual weakening primitive. -/
theorem right_allLabels (P : Primitive → Prop) (d : Nat) (s : ShareSort)
    (weakening : P (.weakening s)) : AllLabels P (right d s) :=
  Translation.allLabels_primitive P d _ weakening

theorem Step.focusFree {d I O} {G H : Hypernet d I O} (step : Step G H) :
    FocusFree G ∧ FocusFree H := by
  cases step with
  | idem s =>
    exact ⟨left_allLabels _ _ s (by intro m eq; cases eq) (by intro m eq; cases eq),
      right_allLabels _ _ s (by intro m eq; cases eq)⟩

theorem Step.holeFree {d I O} {G H : Hypernet d I O} (step : Step G H) :
    HoleFree G ∧ HoleFree H := by
  cases step with
  | idem s =>
    exact ⟨left_allLabels _ _ s (by intro h eq; cases eq) (by intro h eq; cases eq),
      right_allLabels _ _ s (by intro h eq; cases eq)⟩

/-- Idem has no external input, for both term and atom instances. -/
theorem Step.input {d I O} {G H : Hypernet d I O} (step : Step G H) : I = [] := by
  cases step
  rfl

theorem UpToIso.focusFree {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f step g => exact ⟨(allLabels_iso_iff _ f).mpr step.focusFree.1,
      (allLabels_iso_iff _ g).mp step.focusFree.2⟩

theorem UpToIso.holeFree {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    HoleFree G ∧ HoleFree H := by
  cases pair with
  | witness f step g => exact ⟨(allLabels_iso_iff _ f).mpr step.holeFree.1,
      (allLabels_iso_iff _ g).mp step.holeFree.2⟩

theorem UpToIso.input {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) : I = [] := by
  cases pair with
  | witness _ step _ => exact step.input

/-- The concrete pre-template contains exactly the literal Idem pairs up to
ordered recursive graph representation. -/
def template : PreTemplate where
  Rel := UpToIso
  focus_free pair := pair.focusFree

/-- The literal pair is an instance of the pre-template without extra premises. -/
theorem literal (d : Nat) (s : ShareSort) : template.Rel (left d s) (right d s) :=
  .witness (DeepIso.refl _) (.idem d s) (DeepIso.refl _)

end Hypernets.Copying.ContractionIdempotence
