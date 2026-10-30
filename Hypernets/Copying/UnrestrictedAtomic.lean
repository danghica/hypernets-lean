import Hypernets.Copying.RetainedAtomic

/-! Retained/deep atomic contributions for unrestricted contexts. Deep bodies
carry genuine paired fillings; no binding-free condition is imposed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
inductive UnrestrictedAtomic (T : PreTemplate) : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Type 1 where
  | iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : UnrestrictedAtomic T G H
  | deep {d n k h I O} {G H : Hypernet (d+1) I O}
      (hi : [.thunk n] = I) (ho : environmentInterface k h = O)
      {B C : Hypernet d [.term] (environmentInterface (n+k) h)}
      (left : DeepIso G ((box (bound := n) (freeVariables := k) B).reboundary hi ho))
      (body : FillingWitness T B C)
      (right : DeepIso ((box (bound := n) (freeVariables := k) C).reboundary hi ho) H) :
      UnrestrictedAtomic T G H

namespace UnrestrictedAtomic
variable {T : PreTemplate}

def congr {d I O} {G H A B : Hypernet d I O} (pair : UnrestrictedAtomic T G H)
    (f : DeepIso A G) (g : DeepIso H B) : UnrestrictedAtomic T A B := by
  cases pair with
  | iso h => exact .iso (f.trans (h.trans g))
  | deep hi ho l body r => exact .deep hi ho (f.trans l) body (r.trans g)

def interfaces {d I O J K} {G H : Hypernet d I O} (pair : UnrestrictedAtomic T G H)
    (hi : I = J) (ho : O = K) : UnrestrictedAtomic T (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using pair

noncomputable def primitiveIso {d I O} {G H : Hypernet d I O} (pair : UnrestrictedAtomic T G H)
    (primitive : BoxPermutation.PrimitiveFootprint G) : DeepIso G H := by
  cases pair with
  | iso f => exact f
  | deep hi ho left body right =>
    apply False.elim
    obtain ⟨p,label⟩ := primitive (left.edges.invFun (0 : Fin 1))
    have eq := left.edge_label (left.edges.invFun (0 : Fin 1))
    rw [left.edges.right_inv,label] at eq
    exact eq

inductive BoxView {d n k h} (B : Hypernet d [.term] (environmentInterface (n+k) h)) :
    Hypernet (d+1) [.thunk n] (environmentInterface k h) → Type 1 where
  | retained {H} (iso : DeepIso (box (bound := n) (freeVariables := k) B) H) : BoxView B H
  | deep {C H} (body : FillingWitness T B C)
      (iso : DeepIso (box (bound := n) (freeVariables := k) C) H) : BoxView B H

noncomputable def boxView {d n k h}
    {B : Hypernet d [.term] (environmentInterface (n+k) h)}
    {H : Hypernet (d+1) [.thunk n] (environmentInterface k h)}
    (pair : UnrestrictedAtomic T (box (bound := n) (freeVariables := k) B) H) : BoxView (T := T) B H := by
  apply Classical.choice
  cases pair with
  | iso f => exact ⟨.retained f⟩
  | @deep d n' k' h' I O G H hi ho A C left body right =>
    have related := left.edge_label (0 : Fin 1)
    change BoxRelated (alphabet d) (fun X Y => Nonempty (DeepIso X Y))
      ⟨n,k,h,B⟩ ⟨n',k',h',A⟩ at related
    cases related with
    | bodies iso =>
      obtain ⟨f⟩ := iso
      exact ⟨.deep (body.congr f.symm (DeepIso.refl _))
        (by simpa only [Net.reboundary_refl] using right)⟩

/-- Extract exactly the retained/deep contribution selected by an original
edge certificate; the original boxed-body context is retained by equality. -/
noncomputable def of_edge {d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e) (free : FocusFree C)
    (avoid : ∀ h, C.edgeLabel e ≠ primitiveLabel d (.hole h)) : UnrestrictedAtomic T (L e) (R e) := by
  apply Classical.choice
  cases cert with
  | retained l r => exact ⟨.iso (l.iso r (labelEquiv_refl _ _))⟩
  | filled h label rel => exact False.elim (avoid h label)
  | boxed b label inner l r =>
    have bodyFree : FocusFree b.body := by
      have p := free e
      rw [label] at p
      exact p
    let body := FillingWitness.ofDeepFillingExact bodyFree inner (DeepIso.refl _) (DeepIso.refl _)
    exact ⟨.deep l.input l.output
      (((LabelCopy.corolla _).reboundary l.input l.output).iso l (labelEquiv_refl _ _)).symm
      body.1
      (((LabelCopy.corolla _).reboundary r.input r.output).iso r (labelEquiv_refl _ _))⟩

end UnrestrictedAtomic
end Hypernets.Copying
