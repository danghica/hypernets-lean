import Hypernets.Copying.ClosedTranslationUnits
import Hypernets.Copying.ClosedBranchSerial
import Hypernets.Copying.PaddingConstructors

/-! Exact outer graph geometry of the unchanged left-hand Proposition 12.2
term, and the separation of the stable instance from its allocated store. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2
open Graph

/-- The literal body of the outer let binder, with x still its sole free variable. -/
def bodyTerm : Term 1 0 :=
  .lam (.app (.lam (.unary .deref (.var 2))) (.app (.var 0) (.const .unit)))

def body : Hypernet 2 [.term] (environmentInterface 1 0) := Translation.term bodyTerm

def numeral (d : Nat) : Hypernet d [.term] [] := primitiveNet d (.operation (.const (.nat 1)))

theorem padTo_primitive (p : Primitive) (d n : Nat) (bound : d ≤ n) :
    Translation.padTo n bound (primitiveNet d p) = primitiveNet n p := by
  induction bound with
  | refl => exact Translation.padTo_self _
  | @step n bound ih => rw [Translation.padTo_succ _ n bound,ih,Padding.primitive]

noncomputable def constant_padding (d : Nat) (c : Constant) :
    DeepIso (Translation.padTo d (Nat.zero_le d) (Translation.constant 0 0 0 c))
      (primitiveNet d (.operation (.const c))) := by
  have f := Translation.padTo_congr d (Nat.zero_le d) (ClosedTranslation.constant 0 c)
  rw [padTo_primitive] at f
  exact f

/-- Original translation normalized only by boundary-fixing representation isomorphisms. -/
noncomputable def source_iso : DeepIso (Translation.privateCell 0 0)
    (Application.before body (Allocation.before (numeral 3))) := by
  change DeepIso (Translation.application (k := 0) (h := 0)
    (Translation.padTo 3 _ (Translation.abstraction body))
    (Translation.padTo 3 _ (Translation.unary (k := 0) (h := 0) .ref (Translation.constant 0 0 0 (.nat 1))))) _
  rw [Translation.padTo_self]
  have arg := (Padding.unary_to .ref (Translation.constant 0 0 0 (.nat 1)) 3 (by decide)).trans
    ((ClosedTranslation.unary .ref _).trans (Serial.congr (DeepIso.refl _) (constant_padding 3 (.nat 1))))
  exact (ClosedTranslation.application _ _).trans
    (Serial.congr (DeepIso.refl _) (BoxPermutation.tensor_congr (ClosedTranslation.abstraction body) arg))

/-- The common store suffix retains the full canonical one-use atom tree. -/
def storeSuffix (d : Nat) : Hypernet d [.atom] [] :=
  Serial.net (Serial.net (CanonicalTree.atDepth .atom 1 d) (primitiveNet d .store)) (numeral d)

def allocated : Hypernet 3 [.term] [] := Application.before body (Allocation.after (numeral 3))

/-- The beta match consumes only the stable instance; the store stays outside. -/
def betaSource : Hypernet 3 [.term] [] :=
  Serial.net (Application.before body (primitiveNet 3 .instanceEdge)) (storeSuffix 3)

/-- The actual opened body is still connected to the very same allocated store. -/
def opened : Hypernet 3 [.term] [] :=
  Serial.net (Application.after body (primitiveNet 3 .instanceEdge)) (storeSuffix 3)

noncomputable def allocated_argument_iso (d : Nat) :
    DeepIso (Allocation.after (numeral d))
      (Serial.net (primitiveNet d .instanceEdge) (storeSuffix d)) :=
  (Serial.Association.iso (Serial.net (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d))
    (primitiveNet d .store) (numeral d)).trans
      ((Serial.Association.iso (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d)
        (Serial.net (primitiveNet d .store) (numeral d))).trans
          (Serial.congr (DeepIso.refl _) (Serial.Association.iso _ _ _).symm))

noncomputable def allocated_iso : DeepIso allocated betaSource :=
  (Serial.congr (DeepIso.refl _) (BoxPermutation.tensor_congr (DeepIso.refl _)
    (allocated_argument_iso 3))).trans
      ((Serial.congr (DeepIso.refl _) (ClosedBranchSerial.iso (Application.closure body)
        (primitiveNet 3 .instanceEdge) (storeSuffix 3)).symm).trans
          (Serial.Association.iso _ _ _).symm)
end Hypernets.Copying.Proposition12_2
