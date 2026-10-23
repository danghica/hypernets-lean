import Hypernets.Graph.PlugIsomorphism

/-! Incidence isomorphisms with edge labels compared by a supplied relation. -/
namespace Hypernets.Graph.Net
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- Boundary-preserving carrier bijections and ordered incidence preservation,
with related edge labels rather than literal equality of labels. -/
structure RelIso (R : Op → Op → Prop) (G H : Net σ I O) where
  vertices : Bijection G.Internal H.Internal
  edges : Bijection G.Edge H.Edge
  internal_label : ∀ v, H.internalLabel (vertices.toFun v) = G.internalLabel v
  edge_label : ∀ e, R (G.edgeLabel e) (H.edgeLabel (edges.toFun e))
  source : ∀ e, (G.source e).map (Port.map vertices.toFun) = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map (Port.map vertices.toFun) = H.target (edges.toFun e)

namespace RelIso

variable {R : Op → Op → Prop} {G H K : Net σ I O}

def refl (reflexive : ∀ a, R a a) (G : Net σ I O) : RelIso R G G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := reflexive (G.edgeLabel e)
  source e := by simp [Bijection.refl]
  target e := by simp [Bijection.refl]

def symm (symmetric : ∀ {a b}, R a b → R b a) (f : RelIso R G H) : RelIso R H G where
  vertices := f.vertices.symm
  edges := f.edges.symm
  internal_label v := by simpa [Bijection.symm, f.vertices.right_inv] using (f.internal_label (f.vertices.invFun v)).symm
  edge_label e := by simpa [Bijection.symm, f.edges.right_inv] using symmetric (f.edge_label (f.edges.invFun e))
  source e := by
    have h := congrArg (List.map (Port.map f.vertices.invFun)) (f.source (f.edges.invFun e))
    have inv : ∀ v : G.Vertex, Port.map f.vertices.invFun (Port.map f.vertices.toFun v) = v :=
      (Port.bijection f.vertices).left_inv
    simpa [List.map_map, Function.comp_def, inv, f.edges.right_inv, Bijection.symm] using h.symm
  target e := by
    have h := congrArg (List.map (Port.map f.vertices.invFun)) (f.target (f.edges.invFun e))
    have inv : ∀ v : G.Vertex, Port.map f.vertices.invFun (Port.map f.vertices.toFun v) = v :=
      (Port.bijection f.vertices).left_inv
    simpa [List.map_map, Function.comp_def, inv, f.edges.right_inv, Bijection.symm] using h.symm

def trans (transitive : ∀ {a b c}, R a b → R b c → R a c) (f : RelIso R G H) (g : RelIso R H K) : RelIso R G K where
  vertices := f.vertices.trans g.vertices
  edges := f.edges.trans g.edges
  internal_label v := (g.internal_label _).trans (f.internal_label v)
  edge_label e := transitive (f.edge_label e) (g.edge_label _)
  source e := by
    calc
      _ = ((G.source e).map (Port.map f.vertices.toFun)).map (Port.map g.vertices.toFun) := by
        rw [List.map_map]
        congr 1; funext v; cases v <;> rfl
      _ = _ := by rw [f.source, g.source]; rfl
  target e := by
    calc
      _ = ((G.target e).map (Port.map f.vertices.toFun)).map (Port.map g.vertices.toFun) := by
        rw [List.map_map]
        congr 1; funext v; cases v <;> rfl
      _ = _ := by rw [f.target, g.target]; rfl

theorem adjacent_iff (f : RelIso R G H) (e e' : G.Edge) :
    H.Adjacent (f.edges.toFun e) (f.edges.toFun e') ↔ G.Adjacent e e' := by
  constructor
  · rintro ⟨v, hv, hw⟩
    rw [← f.target] at hv
    rw [← f.source] at hw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hw
    have ab := (Port.bijection f.vertices).injective eq
    subst b
    exact ⟨a, ha, hb⟩
  · rintro ⟨v, hv, hw⟩
    refine ⟨Port.map f.vertices.toFun v, ?_, ?_⟩
    · rw [← f.target]; exact List.mem_map_of_mem hv
    · rw [← f.source]; exact List.mem_map_of_mem hw

theorem path_iff (f : RelIso R G H) (es : List G.Edge) :
    H.Path (es.map f.edges.toFun) ↔ G.Path es :=
  path_map_iff f.edges.toFun f.adjacent_iff es


/-- Every ordinary graph isomorphism respects a reflexive label relation. -/
def ofIso {R : Op → Op → Prop} {G H : Net σ I O}
    (reflexive : ∀ a, R a a) (f : Iso G H) : RelIso R G H where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := by rw [f.edge_label]; exact reflexive _
  source := f.source
  target := f.target

end RelIso
end Hypernets.Graph.Net
