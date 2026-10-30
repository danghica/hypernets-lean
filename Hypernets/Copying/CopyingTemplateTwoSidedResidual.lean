import Hypernets.Copying.CopyingTemplateResidualExpansion

/-! Original copying specimens with independent exact sharing corrections on
both endpoints. Reassociation of an actual residual tree is a proved sharing
step, not an equality assumption or an extension of the copying relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined
open BoxPullWeakening (PointedWitness)

/-- A leading sharing correction followed by the original copying relation
and its trailing sharing correction. All three links are actual fillings. -/
structure TwoSidedResidual {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  middle : Hypernet d I O
  point : middle.Vertex
  leading : PointedWitness SharingTreeAlgebra.template G v middle point
  rest : Residual middle point H w

/-- Equality transport changes no graph, ordered attachment, or proof link. -/
noncomputable def Residual.cast {d I O} {G H A B : Hypernet d I O} {v w}
    (p : Residual G v H w) (left : G = A) (right : H = B) :
    Residual A (PointedWitness.castVertex left v) B (PointedWitness.castVertex right w) := by
  subst A; subst B
  simpa only [PointedWitness.castVertex_refl] using p

namespace TwoSidedResidual
/-- A residual needing no leading reassociation uses a literal identity link. -/
noncomputable def ofResidual {d I O} {G H : Hypernet d I O} {v w}
    (p : Residual G v H w) : TwoSidedResidual G v H w :=
  ⟨G,v,PointedWitness.refl G p.paired.filling.focusFree.1 v,p⟩

/-- Independent recursive representation changes act only on actual endpoints. -/
noncomputable def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : TwoSidedResidual G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    TwoSidedResidual A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) := by
  refine ⟨p.middle,p.point,?_,?_⟩
  · have q := p.leading.congr f (DeepIso.refl _)
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q
  · have q := p.rest.congr (DeepIso.refl _) g
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

/-- Untouched components retain their original copying certificates, while
leading sharing acts reflexively on each untouched original left component. -/
noncomputable def expandSelected {d I O} (C : Hypernet d I O)
    (G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (G e).Vertex} {w : (H e).Vertex} (p : TwoSidedResidual (G e) v (H e) w)
    (others : ∀ b, b ≠ e → FillingWitness template (G b) (H b)) :
    TwoSidedResidual (C.expand G) (Net.Expansion.insert C G e v)
      (C.expand H) (Net.Expansion.insert C H e w) := by
  let M := BoxPermutation.PointedFilling.replace C G e p.middle
  have middle : p.middle = M e := (BoxPermutation.PointedFilling.replace_selected C G e p.middle).symm
  let lead := p.leading.cast rfl middle
  let rest := p.rest.cast middle rfl
  have otherLead (b) (ne : b ≠ e) : FillingWitness SharingTreeAlgebra.template (G b) (M b) := by
    simpa only [M,BoxPermutation.PointedFilling.replace_other C G e p.middle b ne] using
      FillingWitness.refl (T := SharingTreeAlgebra.template) (G b) (others b ne).focusFree.1
  have otherRest (b) (ne : b ≠ e) : FillingWitness template (M b) (H b) := by
    simpa only [M,BoxPermutation.PointedFilling.replace_other C G e p.middle b ne] using others b ne
  refine ⟨C.expand M,Net.Expansion.insert C M e (PointedWitness.castVertex middle p.point),?_,?_⟩
  · have q := PointedWitness.expandSelected C G M e lead otherLead
    simpa only [PointedWitness.castVertex_refl] using q
  · have q := Residual.expandSelected C M H e rest otherRest
    simpa only [PointedWitness.castVertex_refl] using q

/-- Both exact sharing corrections apply to the unchanged original specimen.
Its intermediate roots are derived from actual endpoint search histories. -/
theorem quasi_equiv {d} {G H : Hypernet d [.term] []} {v w}
    (p : TwoSidedResidual G v H w) (left : HoleFree G)
    (typed : G.vertexLabel v = .term) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Equiv CostOrder.exact) (StateClass.machine.Equiv CostOrder.exact)
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro lroot rroot
  have midClosed := p.leading.sharing_holeFree.mp left
  have midTyped := p.leading.labels.symm.trans typed
  obtain ⟨correction,midRoot⟩ := p.leading.sharing_exact left typed lroot
  obtain ⟨S,mode,sl,sr,l,r⟩ := p.rest.quasi_equiv midClosed midTyped midRoot rroot
  exact ⟨S,mode,sl,sr,⟨correction.1.trans l.1,l.2.trans correction.2⟩,r⟩

end TwoSidedResidual
end Hypernets.Copying.CopyingTemplate
