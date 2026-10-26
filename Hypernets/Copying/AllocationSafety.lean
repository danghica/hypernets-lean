import Hypernets.Copying.AllocationLocality

/-! Allocation preserves global focus/hole freedom and the stable payload,
not stability of the entire graph containing the new store. -/
namespace Hypernets.Copying.Allocation
open Graph

/-- The allocation prefix introduces exactly the four prescribed primitive kinds. -/
theorem prefix_labels (P : Primitive → Prop) (d : Nat) (inst : P .instanceEdge)
    (weak : P (.weakening .atom)) (contr : P (.contraction .atom)) (cell : P .store) :
    AllLabels P (cellPrefix d) := by
  apply Serial.allLabels_net
  · apply Serial.allLabels_net
    · exact Translation.allLabels_primitive P d .instanceEdge inst
    · intro e
      cases d
      all_goals
        change P (CanonicalTree.label .atom e)
        simp only [CanonicalTree.label]
        split
        · exact weak
        · exact contr
  · exact Translation.allLabels_primitive P d .store cell

theorem after_labels (P : Primitive → Prop) {d O} (G : Hypernet d [.term] O)
    (old : AllLabels P G) (inst : P .instanceEdge) (weak : P (.weakening .atom))
    (contr : P (.contraction .atom)) (cell : P .store) : AllLabels P (after G) :=
  Serial.allLabels_net P (prefix_labels P d inst weak contr cell) old

/-- No hidden focus edge is introduced by the token-coordinate compute rule. -/
theorem after_focusFree {d O} (G : Hypernet d [.term] O) (free : FocusFree G) : FocusFree (after G) :=
  after_labels _ G free (by intro m h; cases h) (by intro m h; cases h)
    (by intro m h; cases h) (by intro m h; cases h)

theorem after_holeFree {d O} (G : Hypernet d [.term] O) (free : HoleFree G) : HoleFree (after G) :=
  after_labels _ G free (by intro h eq; cases eq) (by intro h eq; cases eq)
    (by intro h eq; cases eq) (by intro h eq; cases eq)

/-- Stable arguments imply well-formed focus-free and hole-free allocated graphs. -/
theorem stable_allocation_safe {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
    FocusFree (after G) ∧ HoleFree (after G) :=
  ⟨after_focusFree G stable.focusFree,after_holeFree G stable.holeFree⟩

/-- The stable condition belongs to the stored argument, not to the entire heap graph. -/
theorem after_not_stable {d O} (G : Hypernet d [.term] O) : ¬ Stable (after G) := by
  intro stable
  obtain ⟨p,label,hp⟩ := stable.labels (store G)
  have eq := primitiveLabel_injective d ((store_label G).symm.trans label)
  subst p
  exact hp
end Hypernets.Copying.Allocation
