import Hypernets.Copying.DereferenceTransport

/-! Global safety of the new read fragments and preservation of attached contents. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

/-- Primitive labels remain primitive at every allowance. -/
theorem label_primitive (P : Primitive → Prop) (d : Nat) (p : Primitive) :
    LabelAll P d (primitiveLabel d p) ↔ P p := by cases d <;> rfl

theorem before_labels (P : Primitive → Prop) {h} (T : ContractionTree .atom (h+1)) (d : Nat)
    (read : P (.operation (.unary .deref))) (inst : P .instanceEdge) (store : P .store)
    (weak : P (.weakening .atom)) (contr : P (.contraction .atom)) : AllLabels P (before T d) := by
  rintro ⟨e,x⟩
  apply (label_primitive P d _).mpr
  cases e with
  | reader => exact read
  | inst => exact inst
  | store => exact store
  | tree =>
    change P (T.net.edgeLabel x)
    rcases T.labels x with eq | eq <;> simp_all

theorem after_labels (P : Primitive → Prop) {h} (T : ContractionTree .atom (h+1)) (d : Nat)
    (inst : P .instanceEdge) (store : P .store) (weak : ∀ s, P (.weakening s))
    (contr : ∀ s, P (.contraction s)) : AllLabels P (after T d) := by
  rintro ⟨e,x⟩
  apply (label_primitive P d _).mpr
  cases e with
  | discard => exact weak .term
  | inst => exact inst
  | store => exact store
  | tree =>
    change P (T.net.edgeLabel x)
    rcases T.labels x with eq | eq <;> simp_all
  | share =>
    change P (CanonicalTree.label .term x)
    simp only [CanonicalTree.label]; split
    · exact weak .term
    · exact contr .term

theorem focusFree_sides {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    FocusFree (before T d) ∧ FocusFree (after T d) := by
  constructor
  · exact before_labels _ T d (by intro m h; cases h) (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T d (by intro m h; cases h) (by intro m h; cases h)
      (by intro s m h; cases h) (by intro s m h; cases h)

theorem holeFree_sides {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    HoleFree (before T d) ∧ HoleFree (after T d) := by
  constructor
  · exact before_labels _ T d (by intro m h; cases h) (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T d (by intro m h; cases h) (by intro m h; cases h)
      (by intro s m h; cases h) (by intro s m h; cases h)

/-- Reading may be attached to arbitrary stored contents, including a cyclic host. -/
def withContent {h d O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :=
  Serial.net (after T d) G

theorem content_label {h d O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : G.Edge) :
    (withContent T G).edgeLabel (Serial.rightEdge (after T d) G e) = G.edgeLabel e :=
  Serial.rightEdge_label _ _ _

/-- The copied/shared output remains attached to exactly the old content input. -/
theorem content_attachment {h d O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (withContent T G).target (Serial.leftEdge (after T d) G ⟨.share,(1 : Fin 3)⟩) =
      [BoundarySerial.rightInsert (after T d) G (.input 0)] := by cases d <;> rfl

/-- Arbitrary attached contents cannot redirect lookup away from the retained store. -/
theorem content_store_unique {h d O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) {e n}
    (res : StoreTrace.Resolves (withContent T G) (Serial.leftEdge (after T d) G (afterInstance T d)) e n) :
    e = Serial.leftEdge (after T d) G (afterStore T d) := by
  obtain ⟨k,_,a⟩ := resolves_both T d
  exact (StoreTrace.resolves_unique res (StoreTrace.resolves_serial_left _ _ a)).1
end Hypernets.Copying.Dereference
