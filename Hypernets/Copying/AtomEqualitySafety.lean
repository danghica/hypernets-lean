import Hypernets.Copying.AtomEqualityPreservation

/-! The comparison fragments introduce no focus or hole labels at any depth. -/
namespace Hypernets.Copying.AtomEquality
open Graph
namespace Same
theorem before_labels (P : Primitive → Prop) {h} (T : ContractionTree .atom (h+2)) (d : Nat)
    (op : P (.operation (.binary .atomEq))) (inst : P .instanceEdge) (store : P .store)
    (weak : ∀ s, P (.weakening s)) (contr : P (.contraction .atom)) : AllLabels P (before T d) := by
  rintro ⟨e,x⟩
  apply (Dereference.label_primitive P d _).mpr
  cases e
  · exact op
  · exact inst
  · exact inst
  · change P (T.net.edgeLabel x)
    rcases T.labels x with eq | eq <;> simp_all
  · exact store
theorem after_labels (P : Primitive → Prop) {h} (T : ContractionTree .atom (h+2)) (d : Nat)
    (op : P (.operation (.const (.bool true)))) (inst : P .instanceEdge) (store : P .store)
    (weak : ∀ s, P (.weakening s)) (contr : P (.contraction .atom)) : AllLabels P (after T d) := by
  rintro ⟨e,x⟩
  apply (Dereference.label_primitive P d _).mpr
  cases e
  · exact op
  · exact weak .term
  · exact weak .term
  · exact inst
  · exact inst
  · change P (T.net.edgeLabel x)
    rcases T.labels x with eq | eq <;> simp_all
  · exact store
theorem focusFree_sides {h} (T : ContractionTree .atom (h+2)) (d : Nat) : FocusFree (before T d) ∧ FocusFree (after T d) := by
  constructor
  · exact before_labels _ T d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
theorem holeFree_sides {h} (T : ContractionTree .atom (h+2)) (d : Nat) : HoleFree (before T d) ∧ HoleFree (after T d) := by
  constructor
  · exact before_labels _ T d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
end Same
namespace Different
theorem before_labels (P : Primitive → Prop) {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat)
    (op : P (.operation (.binary .atomEq))) (inst : P .instanceEdge) (store : P .store)
    (weak : ∀ s, P (.weakening s)) (contr : P (.contraction .atom)) : AllLabels P (before T U d) := by
  rintro ⟨e,x⟩
  apply (Dereference.label_primitive P d _).mpr
  cases e
  · exact op
  · exact inst
  · exact inst
  · change P (T.net.edgeLabel x)
    rcases T.labels x with eq | eq <;> simp_all
  · exact store
  · change P (U.net.edgeLabel x)
    rcases U.labels x with eq | eq <;> simp_all
  · exact store
theorem after_labels (P : Primitive → Prop) {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat)
    (op : P (.operation (.const (.bool false)))) (inst : P .instanceEdge) (store : P .store)
    (weak : ∀ s, P (.weakening s)) (contr : P (.contraction .atom)) : AllLabels P (after T U d) := by
  rintro ⟨e,x⟩
  apply (Dereference.label_primitive P d _).mpr
  cases e
  · exact op
  · exact weak .term
  · exact weak .term
  · exact inst
  · exact inst
  · change P (T.net.edgeLabel x)
    rcases T.labels x with eq | eq <;> simp_all
  · exact store
  · change P (U.net.edgeLabel x)
    rcases U.labels x with eq | eq <;> simp_all
  · exact store
theorem focusFree_sides {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : FocusFree (before T U d) ∧ FocusFree (after T U d) := by
  constructor
  · exact before_labels _ T U d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T U d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
theorem holeFree_sides {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : HoleFree (before T U d) ∧ HoleFree (after T U d) := by
  constructor
  · exact before_labels _ T U d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T U d (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
end Different
end Hypernets.Copying.AtomEquality
