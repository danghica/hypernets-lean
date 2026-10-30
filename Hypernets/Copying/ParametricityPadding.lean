import Hypernets.Copying.ParametricityTemplate
import Hypernets.Copying.BoxPermutationPadding
import Hypernets.Copying.PaddingPredicates

/-! Literal Figure 20 is closed under the original depth padding. Every
ordered family, private sharing tree, distributor, box and store is retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph

private def lambda_congr {d k h} {G H : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : DeepIso G H) : DeepIso (lambdaPayload G) (lambdaPayload H) :=
  Serial.congr (DeepIso.refl _) (box_congr (Translation.castInterfaces_congr _ _ f))

theorem readBody_raise (d : Nat) : Copying.raise d (readBody d) = readBody (d+1) := by
  unfold readBody
  rw [BoxPullWeakening.adjoin_raise,Padding.primitive]

theorem oneBody_raise (d : Nat) : Copying.raise d (oneBody d) = oneBody (d+1) := by
  unfold oneBody
  rw [BoxPullWeakening.adjoin_raise,Padding.primitive]

noncomputable def smallLeft_raise (d : Nat) : DeepIso (Copying.raise (d+1) (smallLeft d)) (smallLeft (d+1)) := by
  simpa only [smallLeft,readBody_raise] using Copyable.raise_lambdaPayload (readBody d)

noncomputable def smallRight_raise (d : Nat) : DeepIso (Copying.raise (d+1) (smallRight d)) (smallRight (d+1)) := by
  simpa only [smallRight,oneBody_raise] using Copyable.raise_lambdaPayload (oneBody d)

noncomputable def callback_raise (d : Nat) : DeepIso (Copying.raise d (callback d)) (callback (d+1)) := by
  have iso := Padding.serial (primitiveNet d (.operation .app))
    (Net.Tensor.net (CanonicalTree.atDepth .term 1 d) (primitiveNet d (.operation (.const .unit))))
  rw [Padding.primitive,Padding.tensor,Padding.primitive] at iso
  have tree : Copying.raise d (CanonicalTree.atDepth .term 1 d) = CanonicalTree.atDepth .term 1 (d+1) := by
    cases d <;> rfl
  rw [tree] at iso
  exact iso

noncomputable def callReadBody_raise (d : Nat) :
    DeepIso (Copying.raise (d+1) (callReadBody d)) (callReadBody (d+1)) := by
  unfold callReadBody
  rw [InterfacePermutation.raise]
  apply InterfacePermutation.congr
  have iso := Padding.serial (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (smallLeft d) (callback (d+1)))
  rw [Padding.primitive,Padding.tensor] at iso
  exact iso.trans (Serial.congr (DeepIso.refl _)
    (ParallelPair.congr _ (smallLeft_raise d) (callback_raise (d+1))))

noncomputable def callOneBody_raise (d : Nat) :
    DeepIso (Copying.raise (d+1) (callOneBody d)) (callOneBody (d+1)) := by
  have iso := Padding.serial (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (smallRight d) (callback (d+1)))
  rw [Padding.primitive,Padding.tensor] at iso
  exact iso.trans (Serial.congr (DeepIso.refl _)
    (ParallelPair.congr _ (smallRight_raise d) (callback_raise (d+1))))

noncomputable def largeLeft_raise (d : Nat) : DeepIso (Copying.raise (d+2) (largeLeft d)) (largeLeft (d+1)) :=
  (Copyable.raise_lambdaPayload (callReadBody d)).trans (lambda_congr (callReadBody_raise d))

noncomputable def largeRight_raise (d : Nat) : DeepIso (Copying.raise (d+2) (largeRight d)) (largeRight (d+1)) :=
  (Copyable.raise_lambdaPayload (callOneBody d)).trans (lambda_congr (callOneBody_raise d))

def copies_congr {d k} {G H : Hypernet d [.term] (List.replicate k .term)}
    (f : DeepIso G H) (m : Nat) : DeepIso (copies G m) (copies H m) := by
  induction m with
  | zero => exact DeepIso.refl _
  | succ m ih => exact CopyRule.reboundaryIso (ParallelPair.congr _ f ih) _ _

noncomputable def copies_raise {d k} (G : Hypernet d [.term] (List.replicate k .term))
    (m : Nat) : DeepIso (Copying.raise d (copies G m)) (copies (Copying.raise d G) m) := by
  induction m with
  | zero =>
    cases d
    all_goals exact {
      vertices := Bijection.refl Empty
      edges := Bijection.refl Empty
      internal_label v := nomatch v
      edge_label e := nomatch e
      source e := nomatch e
      target e := nomatch e }
  | succ m ih =>
    unfold copies
    rw [CopyRule.raise_reboundary,Padding.tensor]
    exact CopyRule.reboundaryIso (ParallelPair.congr _ (DeepIso.refl _) ih) _ _

noncomputable def leftFamily_raise (d m₁ m₂ : Nat) :
    DeepIso (Copying.raise (d+2) (leftFamily d m₁ m₂)) (leftFamily (d+1) m₁ m₂) := by
  unfold leftFamily
  rw [CopyRule.raise_reboundary,Padding.tensor]
  exact CopyRule.reboundaryIso (ParallelPair.congr _
    ((copies_raise _ m₁).trans (copies_congr (largeLeft_raise d) m₁))
    ((copies_raise _ m₂).trans (copies_congr (smallLeft_raise (d+1)) m₂))) _ _

noncomputable def rightFamily_raise (d m₁ m₂ : Nat) :
    DeepIso (Copying.raise (d+2) (rightFamily d m₁ m₂)) (rightFamily (d+1) m₁ m₂) := by
  unfold rightFamily
  rw [CopyRule.raise_reboundary,Padding.tensor]
  exact CopyRule.reboundaryIso (ParallelPair.congr _
    ((copies_raise _ m₁).trans (copies_congr (largeRight_raise d) m₁))
    ((copies_raise _ m₂).trans (copies_congr (smallRight_raise (d+1)) m₂))) _ _

noncomputable def privateCell_raise (d : Nat) :
    DeepIso (Copying.raise d (privateCell d)) (privateCell (d+1)) := by
  have iso := Padding.serial (Allocation.cellPrefix d) (primitiveNet d (.operation (.const (.nat 1))))
  rw [Padding.primitive] at iso
  apply iso.trans
  apply Serial.congr _ (DeepIso.refl _)
  have iso := Padding.serial
    (Serial.net (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d)) (primitiveNet d .store)
  rw [Padding.primitive] at iso
  apply iso.trans
  apply Serial.congr _ (DeepIso.refl _)
  have iso := Padding.serial (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d)
  rw [Padding.primitive] at iso
  have tree : Copying.raise d (CanonicalTree.atDepth .atom 1 d) = CanonicalTree.atDepth .atom 1 (d+1) := by
    cases d <;> rfl
  rw [tree] at iso
  exact iso

noncomputable def left_raise {m₁ m₂} (d : Nat) (C : ContractionTree .term (m₁+m₂)) :
    DeepIso (Copying.raise (d+2) (left d C)) (left (d+1) C) := by
  apply (Padding.serial _ _).trans
  apply Serial.congr _ (privateCell_raise (d+2))
  apply (Padding.serial _ _).trans
  apply Serial.congr (leftFamily_raise d m₁ m₂)
  exact DeepIso.refl _

theorem Pair.raise {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    Pair (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f literal g =>
    cases literal with
    | families d C =>
      exact .witness ((Padding.congr f).trans (left_raise d C)) (.families (d+1) C)
        ((rightFamily_raise d _ _).symm.trans (Padding.congr g))

theorem template_paddingClosed : template.PaddingClosed := @Pair.raise

end Hypernets.Copying.Parametricity
