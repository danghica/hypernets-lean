import Hypernets.Copying.DistributorPermutation

/-! Typed graph isomorphisms that may permute the external resource positions.
This does not replace boundary-fixing DeepIso or the observation relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- A bijection of all ports preserves their wire types and boundary roles.
Edge labels still use the original recursive relation and incidences are ordered. -/
structure BoundaryIso {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K) where
  ports : Bijection G.Vertex H.Vertex
  edges : Bijection G.Edge H.Edge
  vertex_label : ∀ v, H.vertexLabel (ports.toFun v) = G.vertexLabel v
  input_iff : ∀ v, (ports.toFun v).IsInput ↔ v.IsInput
  output_iff : ∀ v, (ports.toFun v).IsOutput ↔ v.IsOutput
  edge_label : ∀ e, LabelEquiv d (G.edgeLabel e) (H.edgeLabel (edges.toFun e))
  source : ∀ e, (G.source e).map ports.toFun = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map ports.toFun = H.target (edges.toFun e)

namespace BoundaryIso

def refl {d I O} (G : Hypernet d I O) : BoundaryIso G G where
  ports := Bijection.refl _
  edges := Bijection.refl _
  vertex_label _ := rfl
  input_iff _ := Iff.rfl
  output_iff _ := Iff.rfl
  edge_label _ := labelEquiv_refl _ _
  source _ := by simp [Bijection.refl]
  target _ := by simp [Bijection.refl]

def symm {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) : BoundaryIso H G where
  ports := f.ports.symm
  edges := f.edges.symm
  vertex_label v := by simpa [Bijection.symm,f.ports.right_inv] using (f.vertex_label (f.ports.invFun v)).symm
  input_iff v := by simpa [Bijection.symm,f.ports.right_inv] using (f.input_iff (f.ports.invFun v)).symm
  output_iff v := by simpa [Bijection.symm,f.ports.right_inv] using (f.output_iff (f.ports.invFun v)).symm
  edge_label e := by simpa [Bijection.symm,f.edges.right_inv] using labelEquiv_symm _ (f.edge_label (f.edges.invFun e))
  source e := by
    have eq := congrArg (List.map f.ports.invFun) (f.source (f.edges.invFun e))
    simpa [List.map_map,Function.comp_def,f.ports.left_inv,f.edges.right_inv,Bijection.symm] using eq.symm
  target e := by
    have eq := congrArg (List.map f.ports.invFun) (f.target (f.edges.invFun e))
    simpa [List.map_map,Function.comp_def,f.ports.left_inv,f.edges.right_inv,Bijection.symm] using eq.symm

def trans {d I O J K U V} {G : Hypernet d I O} {H : Hypernet d J K} {F : Hypernet d U V}
    (f : BoundaryIso G H) (g : BoundaryIso H F) : BoundaryIso G F where
  ports := f.ports.trans g.ports
  edges := f.edges.trans g.edges
  vertex_label v := (g.vertex_label _).trans (f.vertex_label v)
  input_iff v := (g.input_iff _).trans (f.input_iff v)
  output_iff v := (g.output_iff _).trans (f.output_iff v)
  edge_label e := labelEquiv_trans _ (f.edge_label e) (g.edge_label _)
  source e := by
    change (G.source e).map (g.ports.toFun ∘ f.ports.toFun) = _
    rw [← List.map_map,f.source,g.source]; rfl
  target e := by
    change (G.target e).map (g.ports.toFun ∘ f.ports.toFun) = _
    rw [← List.map_map,f.target,g.target]; rfl

/-- Ordered-incidence isomorphism preserves and reflects directed adjacency. -/
theorem adjacent_iff {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) (e e' : G.Edge) :
    H.Adjacent (f.edges.toFun e) (f.edges.toFun e') ↔ G.Adjacent e e' := by
  constructor
  · rintro ⟨v,ht,hs⟩
    rw [← f.target] at ht
    rw [← f.source] at hs
    obtain ⟨x,hx,hxv⟩ := List.mem_map.mp ht
    obtain ⟨y,hy,hyv⟩ := List.mem_map.mp hs
    have eq := f.ports.injective (hxv.trans hyv.symm)
    subst y
    exact ⟨x,hx,hy⟩
  · rintro ⟨v,ht,hs⟩
    refine ⟨f.ports.toFun v,?_,?_⟩
    · rw [← f.target]; exact List.mem_map_of_mem ht
    · rw [← f.source]; exact List.mem_map_of_mem hs
/-- Every existing boundary-fixing recursive isomorphism remains valid here. -/
def ofDeepIso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : BoundaryIso G H where
  ports := Port.bijection f.vertices
  edges := f.edges
  vertex_label v := by
    cases v with
    | internal v => exact f.internal_label v
    | input i => rfl
    | output i => rfl
  input_iff v := by cases v <;> rfl
  output_iff v := by cases v <;> rfl
  edge_label := f.edge_label
  source := f.source
  target := f.target

end BoundaryIso
end Hypernets.Copying
