import Hypernets.Copying.ParametricityGraphs

/-! Recursive label invariants of the literal Figure 20 graphs, retaining
every weakening, contraction, box body and private store edge. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph

/-- Exactly the primitive constructors used by the two schematic families
and their shared private cell. This is a syntactic invariant, not a semantic
assumption about arbitrary callbacks supplied by observing contexts. -/
def PrimitiveLabel : Primitive → Prop
  | .operation .lam | .operation .app | .operation (.unary .deref)
  | .operation (.const .unit) | .operation (.const (.nat 1))
  | .weakening _ | .contraction _ | .instanceEdge | .store => True
  | _ => False

private theorem lambda_labels {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (all : AllLabels PrimitiveLabel G) : AllLabels PrimitiveLabel (lambdaPayload G) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial) (by intro e; exact (Translation.allLabels_cast _ _ _ _).mpr all)

private theorem adjoining {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort)
    (all : AllLabels PrimitiveLabel G) : AllLabels PrimitiveLabel (BoxPullWeakening.adjoin G s) :=
  (BoxPullWeakening.insert_allLabels _ G s).mpr ⟨all,trivial⟩

theorem readBody_labels (d : Nat) : AllLabels PrimitiveLabel (readBody d) :=
  adjoining _ _ (Translation.allLabels_primitive _ _ _ trivial)

theorem oneBody_labels (d : Nat) : AllLabels PrimitiveLabel (oneBody d) :=
  adjoining _ _ (Translation.allLabels_primitive _ _ _ trivial)

theorem smallLeft_labels (d : Nat) : AllLabels PrimitiveLabel (smallLeft d) := lambda_labels _ (readBody_labels d)
theorem smallRight_labels (d : Nat) : AllLabels PrimitiveLabel (smallRight d) := lambda_labels _ (oneBody_labels d)

theorem callback_labels (d : Nat) : AllLabels PrimitiveLabel (callback d) := by
  apply Serial.allLabels_net
  · exact Translation.allLabels_primitive _ _ _ trivial
  · apply Translation.allLabels_tensor
    · intro e
      apply (Dereference.label_primitive _ d _).mpr
      change PrimitiveLabel (CanonicalTree.label .term e)
      unfold CanonicalTree.label
      split <;> trivial
    · exact Translation.allLabels_primitive _ _ _ trivial

theorem callReadBody_labels (d : Nat) : AllLabels PrimitiveLabel (callReadBody d) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial)
    (Translation.allLabels_tensor _ (smallLeft_labels d) (callback_labels (d+1)))

theorem callOneBody_labels (d : Nat) : AllLabels PrimitiveLabel (callOneBody d) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial)
    (Translation.allLabels_tensor _ (smallRight_labels d) (callback_labels (d+1)))

theorem largeLeft_labels (d : Nat) : AllLabels PrimitiveLabel (largeLeft d) := lambda_labels _ (callReadBody_labels d)
theorem largeRight_labels (d : Nat) : AllLabels PrimitiveLabel (largeRight d) := lambda_labels _ (callOneBody_labels d)

/-- Replication is finite disjoint assembly; it introduces no primitive. -/
theorem copies_labels {P d k} (G : Hypernet d [.term] (List.replicate k .term))
    (all : AllLabels P G) (m : Nat) : AllLabels P (copies G m) := by
  induction m with
  | zero => intro e; exact nomatch e
  | succ m ih => exact Translation.allLabels_tensor _ all ih

theorem leftFamily_labels (d m₁ m₂ : Nat) : AllLabels PrimitiveLabel (leftFamily d m₁ m₂) :=
  Translation.allLabels_tensor _ (copies_labels _ (largeLeft_labels d) m₁)
    (copies_labels _ (smallLeft_labels (d+1)) m₂)

theorem rightFamily_labels (d m₁ m₂ : Nat) : AllLabels PrimitiveLabel (rightFamily d m₁ m₂) :=
  Translation.allLabels_tensor _ (copies_labels _ (largeRight_labels d) m₁)
    (copies_labels _ (smallRight_labels (d+1)) m₂)

theorem privateCell_labels (d : Nat) : AllLabels PrimitiveLabel (privateCell d) := by
  apply Serial.allLabels_net
  · apply Serial.allLabels_net
    · apply Serial.allLabels_net
      · exact Translation.allLabels_primitive _ _ _ trivial
      · intro e
        apply (Dereference.label_primitive _ d _).mpr
        change PrimitiveLabel (CanonicalTree.label .atom e)
        unfold CanonicalTree.label
        split <;> trivial
    · exact Translation.allLabels_primitive _ _ _ trivial
  · exact Translation.allLabels_primitive _ _ _ trivial

theorem left_labels {m₁ m₂} (d : Nat) (C : ContractionTree .term (m₁+m₂)) :
    AllLabels PrimitiveLabel (left d C) := by
  apply Serial.allLabels_net
  · apply Serial.allLabels_net
    · exact leftFamily_labels d m₁ m₂
    · intro e
      apply (Dereference.label_primitive _ (d+2) _).mpr
      rcases C.labels e with eq | eq <;> rw [eq] <;> trivial
  · exact privateCell_labels (d+2)

theorem right_labels (d m₁ m₂ : Nat) : AllLabels PrimitiveLabel (right d m₁ m₂) :=
  rightFamily_labels d m₁ m₂

/-- The full recursively nested figure is both focus-free and hole-free. -/
theorem labels_closed {d I O} {G : Hypernet d I O} (all : AllLabels PrimitiveLabel G) :
    FocusFree G ∧ HoleFree G := by
  have lift : ∀ d (p : (alphabet d).Symbol), LabelAll PrimitiveLabel d p →
      LabelAll (fun p => ∀ m, p ≠ .focus m) d p ∧ LabelAll (fun p => ∀ h, p ≠ .hole h) d p := by
    intro d
    induction d with
    | zero =>
      rintro ⟨p⟩ good
      constructor
      · intro m eq; cases eq; exact good
      · intro h eq; cases eq; exact good
    | succ d ih =>
      intro p good
      cases p with
      | inl p =>
        constructor
        · intro m eq; cases eq; exact good
        · intro h eq; cases eq; exact good
      | inr b => exact ⟨fun e => (ih _ (good e)).1,fun e => (ih _ (good e)).2⟩
  exact ⟨fun e => (lift d _ (all e)).1,fun e => (lift d _ (all e)).2⟩

end Hypernets.Copying.Parametricity
