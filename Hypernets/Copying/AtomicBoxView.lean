import Hypernets.Copying.AtomicNormalForm

/-! Exhaustive canonical box views with their original shallow and deep evidence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

inductive BoxView {d n k h} (B : Hypernet d [.term] (environmentInterface (n+k) h)) :
    Hypernet (d+1) [.thunk n] (environmentInterface k h) → Type 1 where
  | retained {H} (iso : DeepIso (box (bound := n) (freeVariables := k) B) H) : BoxView B H
  | deep {C H} (body : FillingWitness template B C)
      (iso : DeepIso (box (bound := n) (freeVariables := k) C) H) : BoxView B H
  | shallow {C H} (p : Pair n k h) (body : BoundaryIso B C)
      (action : ∀ i, body.outputs.toFun i = p.body.bijection.toFun i)
      (iso : DeepIso (InterfacePermutation.net (box (bound := n) (freeVariables := k) C) p.outer.symm) H) : BoxView B H

/-- The original atomic case split determines the actual affected box body and
outer port permutation; no replacement complement is postulated. -/
noncomputable def AtomicPair.boxView {d n k h}
    {B : Hypernet d [.term] (environmentInterface (n+k) h)}
    {H : Hypernet (d+1) [.thunk n] (environmentInterface k h)}
    (pair : AtomicPair (box (bound := n) (freeVariables := k) B) H) : BoxView B H := by
  apply Classical.choice
  cases pair.normal with
  | iso f => exact ⟨.retained f⟩
  | @deep d n' k' h' I O G H hi ho A C left body right =>
    have related := left.edge_label (0 : Fin 1)
    change BoxRelated (alphabet d) (fun X Y => Nonempty (DeepIso X Y))
      ⟨n,k,h,B⟩ ⟨n',k',h',A⟩ at related
    cases related with
    | bodies iso =>
      obtain ⟨f⟩ := iso
      exact ⟨.deep (body.congr f.symm (DeepIso.refl _)) (by simpa only [Net.reboundary_refl] using right)⟩
  | @shallow d n' k' h' I O G H hi ho C p left right =>
    have related := left.edge_label (0 : Fin 1)
    change BoxRelated (alphabet d) (fun X Y => Nonempty (DeepIso X Y))
      ⟨n,k,h,B⟩ ⟨n',k',h',InterfacePermutation.net C p.body.symm⟩ at related
    cases related with
    | bodies iso =>
      obtain ⟨f⟩ := iso
      let b := (BoundaryIso.ofDeepIso f).trans (InterfacePermutation.iso C p.body.symm).symm
      refine ⟨.shallow p b ?_ (by simpa only [Net.reboundary_refl] using right)⟩
      intro i
      change p.body.bijection.toFun i = p.body.bijection.toFun i
      rfl
end Hypernets.Copying.BoxPermutation
