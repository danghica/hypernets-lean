import Hypernets.Copying.CopySuccessorLocal

/-! The complete copying presentation commutes with actual source occurrences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule.SuccessorMatch
open Graph Opening
variable {d I O J K k h} {G : Hypernet d I O} {N : Hypernet d J K}
    {H : Hypernet d [.term] (environmentInterface k h)} {v : G.Vertex}

def originPort (f : Occurrence G N) : Port (G.Internal ⊕ AddedVertex H) I.length O.length →
    Port (N.Internal ⊕ AddedVertex H) J.length K.length
  | .internal (.inl x) => .internal (.inl (f.internals x))
  | .internal (.inr x) => .internal (.inr x)
  | .input i => Port.map Sum.inl (f.ports (.input i))
  | .output i => Port.map Sum.inl (f.ports (.output i))

def originEdge (f : Occurrence G N) : G.Edge ⊕ AddedEdge H → N.Edge ⊕ AddedEdge H
  | .inl e => .inl (f.edges e)
  | .inr e => .inr e

theorem origin_old (f : Occurrence G N) (x : G.Vertex) :
    originPort (H := H) f (Port.map Sum.inl x) = Port.map Sum.inl (f.ports x) := by
  cases x <;> simp only [originPort,Port.map,f.internal_map]

theorem copyPort_map (f : Occurrence G N) (x : H.Vertex) :
    originPort f (copyPort (v := v) x) = copyPort (v := f.ports v) x := by
  cases x with
  | internal x => rfl
  | input i => exact origin_old f v
  | output i => rfl

theorem distributorPort_map (a : SuccessorMatch G v H) (f : Occurrence G N)
    (x : (Translation.environmentDistributor d k h 2).Vertex) :
    originPort f (a.distributorPort x) = (a.map f).distributorPort x := by
  cases x with
  | internal x => rfl
  | input i => rfl
  | output i =>
    unfold distributorPort
    rw [origin_old]
    change Port.map Sum.inl (f.ports ((G.target a.tail)[i.val]'_)) =
      Port.map Sum.inl ((N.target (f.edges a.tail))[i.val]'_)
    simp only [← f.target,List.getElem_map]

theorem source_map (a : SuccessorMatch G v H) (f : Occurrence G N) (e : a.presentation.Edge) :
    (a.presentation.source e).map (originPort f) = (a.map f).presentation.source (originEdge f e) := by
  classical
  rcases e with e | (e | (e | e))
  · by_cases eq : e = a.active
    · subst e
      simp only [presentation,originEdge,map,ite_eq_left rfl]
      cases hr : a.right <;> simp [selectedSources,hr,origin_old,weakPort,originPort]
      all_goals cases a.other <;> simp only [Port.map,f.internal_map]
    · have ne : f.edges e ≠ f.edges a.active := fun h => eq (f.edge_injective h)
      simp only [presentation,originEdge,map,ite_eq_right eq,ite_eq_right ne]
      rw [← f.source,List.map_map,List.map_map]
      exact List.map_congr_left (fun p _ => origin_old f p)
  · change ((H.source e).map _).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => copyPort_map f p)
  · rfl
  · change (((Translation.environmentDistributor d k h 2).source e).map _).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => distributorPort_map a f p)

theorem target_map (a : SuccessorMatch G v H) (f : Occurrence G N) (e : a.presentation.Edge) :
    (a.presentation.target e).map (originPort f) = (a.map f).presentation.target (originEdge f e) := by
  classical
  rcases e with e | (e | (e | e))
  · by_cases eq : e = a.tail
    · subst e
      simp only [presentation,originEdge,map,tail,Occurrence.comp,Function.comp_apply,ite_true,ite_eq_left rfl]
      rw [List.map_map]
      rfl
    · have ne : f.edges e ≠ f.edges a.tail := fun h => eq (f.edge_injective h)
      simp only [presentation,originEdge,map,tail,Occurrence.comp,Function.comp_apply] at *
      rw [ite_eq_right eq,ite_eq_right ne,← f.target,List.map_map,List.map_map]
      exact List.map_congr_left (fun p _ => origin_old f p)
  · change ((H.target e).map _).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => copyPort_map f p)
  · rfl
  · change (((Translation.environmentDistributor d k h 2).target e).map _).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => distributorPort_map a f p)

theorem origin_iso {N : Hypernet d I O} (f : DeepIso G N) (p : Port (G.Internal ⊕ AddedVertex H) I.length O.length) :
    originPort (H := H) (Occurrence.ofIso f) p = Port.map (f.vertices.sum (Bijection.refl _)).toFun p := by
  cases p with
  | internal x => cases x <;> rfl
  | input i => rfl
  | output i => rfl

noncomputable def renamePresentation {N : Hypernet d I O} (a : SuccessorMatch G v H) (f : DeepIso G N) :
    a.presentation.Iso (a.map (Occurrence.ofIso f)).presentation where
  vertices := f.vertices.sum (Bijection.refl _)
  edges := f.edges.sum (Bijection.refl _)
  vertex_range _ := Iff.rfl
  edge_range _ := Iff.rfl
  vertex_label := by rintro (x | (x | (x | (x | x)))); exact f.internal_label x; all_goals rfl
  edge_label := by rintro (e | (e | (e | e))); exact f.edge_label e; all_goals exact labelEquiv_refl _ _
  source e := by
    have h := source_map a (Occurrence.ofIso f) e
    have ports : originPort (H := H) (Occurrence.ofIso f) = Port.map (f.vertices.sum (Bijection.refl _)).toFun := funext (origin_iso f)
    rw [ports] at h
    cases e <;> exact h
  target e := by
    have h := target_map a (Occurrence.ofIso f) e
    have ports : originPort (H := H) (Occurrence.ofIso f) = Port.map (f.vertices.sum (Bijection.refl _)).toFun := funext (origin_iso f)
    rw [ports] at h
    cases e <;> exact h
end Hypernets.Copying.CopyRule.SuccessorMatch

namespace Hypernets.Copying.CopyRule.SuccessorCertificate
open Graph Opening
variable {d I O k h} {G K G' K' : Hypernet d I O} {v w}
    {H : Hypernet d [.term] (environmentInterface k h)}

noncomputable def rename (a : SuccessorCertificate G K v w H) (f : DeepIso G G') (g : DeepIso K K') :
    SuccessorCertificate G' K' (Port.map f.vertices.toFun v) (Port.map g.vertices.toFun w) H where
  matched := a.matched.map (Occurrence.ofIso f)
  realization := (a.realization.transport (a.matched.renamePresentation f)).rename g.symm
  token := by
    change Port.map ((f.vertices.sum (Bijection.refl _)).toFun ∘ a.realization.vertices ∘ g.vertices.invFun)
      (Port.map g.vertices.toFun w) = _
    rw [Arithmetic.Reduction.port_comp]
    have inv := (Port.bijection g.vertices).left_inv w
    change Port.map g.vertices.invFun (Port.map g.vertices.toFun w) = w at inv
    rw [Arithmetic.Reduction.port_comp,inv,a.token]
    cases v <;> rfl
end Hypernets.Copying.CopyRule.SuccessorCertificate
