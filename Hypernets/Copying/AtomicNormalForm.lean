import Hypernets.Copying.WholeRewriteTransport

/-! Remove representation and interface wrappers from atomic contributions,
retaining exactly the shallow or deep certificate that drives a box overlap. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

/-- A genuine atomic contribution after collecting all representation changes. -/
inductive AtomicNormal : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Type 1 where
  | iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : AtomicNormal G H
  | shallow {d n k h I O} {G H : Hypernet (d+1) I O}
      (hi : [.thunk n] = I) (ho : environmentInterface k h = O)
      (C : Hypernet d [.term] (environmentInterface (n+k) h)) (p : Pair n k h)
      (left : DeepIso G ((box (bound := n) (freeVariables := k)
        (InterfacePermutation.net C p.body.symm)).reboundary hi ho))
      (right : DeepIso ((InterfacePermutation.net (box (bound := n) (freeVariables := k) C)
        p.outer.symm).reboundary hi ho) H) : AtomicNormal G H
  | deep {d n k h I O} {G H : Hypernet (d+1) I O}
      (hi : [.thunk n] = I) (ho : environmentInterface k h = O)
      {B C : Hypernet d [.term] (environmentInterface (n+k) h)}
      (left : DeepIso G ((box (bound := n) (freeVariables := k) B).reboundary hi ho))
      (body : FillingWitness template B C)
      (right : DeepIso ((box (bound := n) (freeVariables := k) C).reboundary hi ho) H) : AtomicNormal G H

namespace AtomicNormal

noncomputable def congr {d I O} {G H A B : Hypernet d I O} (pair : AtomicNormal G H)
    (f : DeepIso A G) (g : DeepIso H B) : AtomicNormal A B := by
  cases pair with
  | iso h => exact .iso (f.trans (h.trans g))
  | shallow hi ho C p l r => exact .shallow hi ho C p (f.trans l) (r.trans g)
  | deep hi ho l body r => exact .deep hi ho (f.trans l) body (r.trans g)

def interfaces {d I O J K} {G H : Hypernet d I O} (pair : AtomicNormal G H)
    (hi : I = J) (ho : O = K) : AtomicNormal (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using pair
end AtomicNormal

noncomputable def UpToIso.normal {d I O} {G H : Hypernet d I O} (rel : UpToIso G H) :
    AtomicNormal G H := by
  apply Classical.choice
  cases rel with
  | witness left step right =>
    cases step with
    | permute C p => exact ⟨.shallow rfl rfl C p (by simpa only [Net.reboundary_refl] using left)
        (by simpa only [Net.reboundary_refl] using right)⟩

/-- Every certificate extracted from an original specimen has this normal form. -/
noncomputable def AtomicPair.normal {d I O} {G H : Hypernet d I O} (pair : AtomicPair G H) :
    AtomicNormal G H := by
  induction pair with
  | iso f => exact .iso f
  | shallow rel => exact rel.1.normal
  | boxed body =>
    exact .deep rfl rfl (by simpa only [Net.reboundary_refl] using DeepIso.refl _) body
      (by simpa only [Net.reboundary_refl] using DeepIso.refl _)
  | congr f pair g ih => exact ih.congr f g
  | interfaces hi ho pair ih => exact ih.interfaces hi ho
end Hypernets.Copying.BoxPermutation
