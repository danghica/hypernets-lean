import Hypernets.Copying.BoxPullContractionCopying
import Hypernets.Copying.CorollaNormalisation

/-! Atomic certificates for transporting an existing contextual rewrite.
They retain actual BPullC pairs and recursively certified box bodies. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

/-- One outer contribution: representation, the original BPullC pair, or a box
whose bodies have an original recursive filling certificate. The congruence
constructors only change graph representation and equal interface indices. -/
inductive AtomicPair : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Type 1 where
  | iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : AtomicPair G H
  | shallow {d I O} {G H : Hypernet d I O} (pair : template.Rel G H) : AtomicPair G H
  | boxed {d n k h} {B C : Hypernet d [.term] (environmentInterface (n+k) h)}
      (body : FillingWitness template B C) :
      AtomicPair (box (bound := n) (freeVariables := k) B) (box (bound := n) (freeVariables := k) C)
  | congr {d I O} {G H A B : Hypernet d I O} (left : DeepIso A G)
      (pair : AtomicPair G H) (right : DeepIso H B) : AtomicPair A B
  | interfaces {d I O J K} {G H : Hypernet d I O} (hi : I = J) (ho : O = K)
      (pair : AtomicPair G H) : AtomicPair (G.reboundary hi ho) (H.reboundary hi ho)

namespace AtomicPair
/-- Every atomic certificate supplies a genuine recursive residual certificate. -/
noncomputable def witness {d I O} {G H : Hypernet d I O} (pair : AtomicPair G H)
    (free : FocusFree G) : FillingWitness template G H := by
  induction pair with
  | iso f => exact (FillingWitness.refl _ free).congr (DeepIso.refl _) f
  | shallow rel => exact FillingWitness.of_rel 0 rel
  | boxed body => exact body.boxed
  | congr f pair g ih => exact (ih ((allLabels_iso_iff _ f).mp free)).congr f.symm g
  | interfaces hi ho pair ih =>
    cases hi; cases ho
    simpa only [Net.reboundary_refl] using ih free

/-- Primitive footprints cannot contain a shallow or boxed BPullC contribution. -/
theorem primitive_rigid {d I O} {G H : Hypernet d I O} (pair : AtomicPair G H)
    (primitive : BoxPermutation.PrimitiveFootprint G) : Nonempty (DeepIso G H) := by
  induction pair with
  | iso f => exact ⟨f⟩
  | shallow rel =>
    cases rel with
    | witness f step g =>
      cases step with
      | pull s B free =>
        obtain ⟨a,label⟩ := primitive (f.edges.invFun (0 : Fin 1))
        have impossible := f.edge_label (f.edges.invFun (0 : Fin 1))
        rw [label] at impossible
        exact False.elim impossible
  | boxed body =>
    obtain ⟨p,label⟩ := primitive (0 : Fin 1)
    cases label
  | @congr d I O G H A B f pair g ih =>
    have full : BoxPermutation.PrimitiveFootprint G := by
      intro e
      obtain ⟨p,label⟩ := primitive (f.edges.invFun e)
      refine ⟨p,?_⟩
      simpa only [f.edges.right_inv] using (Search.primitive_equiv (f.edge_label _) p).mp label
    obtain ⟨h⟩ := ih full
    exact ⟨f.trans (h.trans g)⟩
  | interfaces hi ho pair ih =>
    cases hi; cases ho
    simpa only [Net.reboundary_refl] using ih primitive
end AtomicPair

/-- Extract the atomic contribution already present at an original context edge. -/
noncomputable def atomic_of_edge {d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge template C L R e) (free : FocusFree C) : AtomicPair (L e) (R e) := by
  classical
  apply Classical.choice
  cases cert with
  | retained l r => exact ⟨.iso (l.iso r (labelEquiv_refl _ _))⟩
  | filled h label rel => exact ⟨.shallow rel⟩
  | boxed b label inner l r =>
    have contextFree : FocusFree b.body := by
      have h := free e
      rw [label] at h
      exact h
    let w := FillingWitness.ofDeepFilling contextFree inner (DeepIso.refl _) (DeepIso.refl _)
    have hi := l.input
    have ho := l.output
    exact ⟨.congr
      (((LabelCopy.corolla _).reboundary hi ho).iso l (labelEquiv_refl _ _)).symm
      ((AtomicPair.boxed w).interfaces hi ho)
      (((LabelCopy.corolla _).reboundary r.input r.output).iso r (labelEquiv_refl _ _))⟩
end Hypernets.Copying.BoxPullContraction
