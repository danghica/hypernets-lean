import Hypernets.Copying.NullaryTemplates
import Hypernets.Copying.MinimalContractionSpine
import Hypernets.Copying.PaddingPredicates

/-! Figure 21's garbage-collection pre-template. An arbitrary zero-input
term contraction tree feeds the original copyable payload; the right side
is exactly the term and atom zero-use distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.GarbageCollection
open Graph

/-- The original discarded graph retains the complete zero-input tree and
the copyable payload, including arbitrary recursive lambda bodies. -/
def left {d k h} (tree : ContractionTree .term 0)
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d [] (environmentInterface k h) := Serial.net (tree.atDepth d) H

/-- The paper's two ordered zero-use distributors, with variables before atoms. -/
def right (d k h : Nat) : Hypernet d [] (environmentInterface k h) :=
  Translation.castInterfaces (by simp [environmentInterface]) rfl
    (Translation.environmentDistributor d k h 0)

/-- The literal GC family of Figure 21. Copyability is retained from the
figure's H convention; focus freedom is the pre-template requirement. -/
inductive Step : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | collect {d k h} (tree : ContractionTree .term 0)
      (H : Hypernet d [.term] (environmentInterface k h))
      (copyable : Copyable H) (free : FocusFree H) :
      Step (left tree H) (right d k h)

/-- Independent graph carrier changes preserve every ordered external port. -/
inductive UpToIso : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (step : Step A B) (right : DeepIso B H) : UpToIso G H

/-- Arbitrary tree presentations contain only their original weakening and
contraction labels when raised into the copying alphabet. -/
theorem tree_allLabels (P : Primitive → Prop) (tree : ContractionTree .term 0) (d : Nat)
    (weakening : P (.weakening .term)) (contraction : P (.contraction .term)) :
    AllLabels P (tree.atDepth d) := by
  intro e
  apply (Dereference.label_primitive P d _).mpr
  rcases tree.labels e with eq | eq <;> simp_all

/-- Serial assembly retains the payload's entire recursive label predicate. -/
theorem left_allLabels (P : Primitive → Prop) {d k h} (tree : ContractionTree .term 0)
    (H : Hypernet d [.term] (environmentInterface k h)) (safe : AllLabels P H)
    (weakening : P (.weakening .term)) (contraction : P (.contraction .term)) :
    AllLabels P (left tree H) :=
  Serial.allLabels_net P (tree_allLabels P tree d weakening contraction) safe

/-- Zero-use distributors satisfy every primitive-label property holding of
the two sorts' sharing primitives, with the literal distributors retained. -/
theorem right_allLabels (P : Primitive → Prop) (d k h : Nat)
    (weakening : ∀ s, P (.weakening s)) (contraction : ∀ s, P (.contraction s)) :
    AllLabels P (right d k h) :=
  (Translation.allLabels_cast P _ _ _).mpr
    (Translation.allLabels_tensor P
      (Distributor.allLabels_atDepth P .term k 0 d (weakening .term) (contraction .term))
      (Distributor.allLabels_atDepth P .atom h 0 d (weakening .atom) (contraction .atom)))

theorem Step.focusFree {d I O} {G H : Hypernet d I O} (step : Step G H) :
    FocusFree G ∧ FocusFree H := by
  cases step with
  | collect tree H copyable free =>
    exact ⟨left_allLabels _ tree H free (by intro m eq; cases eq) (by intro m eq; cases eq),
      right_allLabels _ _ _ _ (by intro s m eq; cases eq) (by intro s m eq; cases eq)⟩

/-- Every literal garbage-collection fragment has empty input interface. -/
theorem Step.input {d I O} {G H : Hypernet d I O} (step : Step G H) : I = [] := by
  cases step
  rfl

theorem UpToIso.focusFree {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f step g => exact ⟨(allLabels_iso_iff _ f).mpr step.focusFree.1,
      (allLabels_iso_iff _ g).mp step.focusFree.2⟩

theorem UpToIso.input {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) : I = [] := by
  cases pair with
  | witness _ step _ => exact step.input

/-- The actual GC pre-template, without any assumed execution equivalence. -/
def template : PreTemplate where
  Rel := UpToIso
  focus_free pair := pair.focusFree

theorem literal {d k h} (tree : ContractionTree .term 0)
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H) (free : FocusFree H) :
    template.Rel (left tree H) (right d k h) :=
  .witness (DeepIso.refl _) (.collect tree H copyable free) (DeepIso.refl _)

end Hypernets.Copying.GarbageCollection
