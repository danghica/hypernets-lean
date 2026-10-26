import Hypernets.Copying.CopyRule

/-! Copying preserves recursive label safety, including inside duplicated boxes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

theorem tree_labels (P : Primitive → Prop) {n} (T : ContractionTree .term (n+1)) (d : Nat)
    (weak : P (.weakening .term)) (contr : P (.contraction .term)) : AllLabels P (tree T d) := by
  intro e; apply (Dereference.label_primitive P d _).mpr
  rcases T.labels e with eq | eq <;> simp_all

theorem residual_allLabels (P : Primitive → Prop) {n} (T : ContractionTree .term (n+1)) (d : Nat)
    (weak : P (.weakening .term)) (contr : P (.contraction .term)) : AllLabels P (residual T d) := by
  rintro ⟨b,e⟩; cases b
  · exact (Dereference.label_primitive P d _).mpr weak
  · exact tree_labels P T d weak contr e

theorem before_allLabels (P : Primitive → Prop) {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (safe : AllLabels P H)
    (weak : P (.weakening .term)) (contr : P (.contraction .term)) : AllLabels P (before T H) :=
  Serial.allLabels_net P (tree_labels P T d weak contr) safe

theorem after_allLabels (P : Primitive → Prop) {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (safe : AllLabels P H)
    (weak : ∀ s, P (.weakening s)) (contr : ∀ s, P (.contraction s)) : AllLabels P (after T H) := by
  apply Serial.allLabels_net P
  · rintro ⟨b,e⟩; cases b
    · exact safe e
    · exact Serial.allLabels_net P (residual_allLabels P T d (weak .term) (contr .term)) safe e
  · exact Translation.allLabels_tensor P
      (Distributor.allLabels_atDepth P .term k 2 d (weak .term) (contr .term))
      (Distributor.allLabels_atDepth P .atom h 2 d (weak .atom) (contr .atom))

theorem focusFree_after {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (safe : FocusFree H) : FocusFree (after T H) :=
  after_allLabels _ T H safe (by intro s m h; cases h) (by intro s m h; cases h)

theorem holeFree_after {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (safe : HoleFree H) : HoleFree (after T H) :=
  after_allLabels _ T H safe (by intro s m h; cases h) (by intro s m h; cases h)
end Hypernets.Copying.CopyRule
