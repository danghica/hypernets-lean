import Hypernets.Copying.AssignmentTransport

/-! Recursive label safety of both assignment sides, with the stable premise retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

theorem before_labels (P : Primitive → Prop) {d h O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (value : AllLabels P G)
    (assign : P (.operation (.binary .assign))) (inst : P .instanceEdge) (store : P .store)
    (weak : P (.weakening .atom)) (contr : P (.contraction .atom)) : AllLabels P (before T G) := by
  cases d <;> apply Serial.allLabels_expand
  all_goals
    intro e; cases e
    · exact Translation.allLabels_primitive P _ _ assign
    · exact Translation.allLabels_primitive P _ _ inst
    · intro x
      change P (T.net.edgeLabel x)
      rcases T.labels x with eq | eq <;> simp_all
    · exact Translation.allLabels_primitive P _ _ store
    · exact value

theorem after_labels (P : Primitive → Prop) {d h O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (value : AllLabels P G)
    (unit : P (.operation (.const .unit))) (inst : P .instanceEdge) (store : P .store)
    (weak : ∀ s, P (.weakening s)) (contr : P (.contraction .atom)) : AllLabels P (after T G) := by
  cases d <;> apply Serial.allLabels_expand
  all_goals
    intro e; cases e
    · exact Translation.allLabels_primitive P _ _ (weak .term)
    · exact Translation.allLabels_primitive P _ _ inst
    · intro x
      change P (T.net.edgeLabel x)
      rcases T.labels x with eq | eq <;> simp_all
    · exact Translation.allLabels_primitive P _ _ store
    · exact value
    · exact Translation.allLabels_primitive P _ _ (weak .term)
    · exact Translation.allLabels_primitive P _ _ unit

theorem stable_assignment_safe {d h O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G) :
    FocusFree (before T G) ∧ HoleFree (before T G) ∧ FocusFree (after T G) ∧ HoleFree (after T G) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact before_labels _ T G stable.focusFree (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro m h; cases h) (by intro m h; cases h)
  · exact before_labels _ T G stable.holeFree (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T G stable.focusFree (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)
  · exact after_labels _ T G stable.holeFree (by intro m h; cases h) (by intro m h; cases h)
      (by intro m h; cases h) (by intro s m h; cases h) (by intro m h; cases h)

/-- Whole-heap stability must not be asserted for an updated graph containing a store. -/
theorem after_not_stable {d O} (T : ContractionTree .atom 1) (G : Hypernet d [.term] O) :
    ¬ Stable (after T G) := by
  intro stable
  obtain ⟨p,label,hp⟩ := stable.labels (afterStore T G)
  have eq := primitiveLabel_injective d ((store_labels T G).2.symm.trans label)
  subst p
  exact hp
end Hypernets.Copying.Assignment
