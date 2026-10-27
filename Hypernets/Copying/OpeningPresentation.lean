import Hypernets.Copying.ArithmeticCoherenceExamples

/-! Partial incidence presentations compare complete results of box opening.
Presentations are proof data, not additional machine states or reduction rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening
open Graph

/-- An ambient collection of occurrences, with predicates selecting the survivors. -/
structure Presentation (d : Nat) (I O : List Wire) where
  Vertex : Type
  Edge : Type
  vertexLabel : Vertex → Wire
  edgeLabel : Edge → (alphabet d).Symbol
  keepVertex : Vertex → Prop
  keepEdge : Edge → Prop
  source : Edge → List (Port Vertex I.length O.length)
  target : Edge → List (Port Vertex I.length O.length)

/-- A graph realizes exactly the selected occurrences and their ordered incidences. -/
structure Realization {d I O} (P : Presentation d I O) (H : Hypernet d I O) where
  vertices : H.Internal → P.Vertex
  edges : H.Edge → P.Edge
  vertex_injective : Function.Injective vertices
  edge_injective : Function.Injective edges
  vertex_range : ∀ x, (∃ y, vertices y = x) ↔ P.keepVertex x
  edge_range : ∀ e, (∃ f, edges f = e) ↔ P.keepEdge e
  internal_label : ∀ x, H.internalLabel x = P.vertexLabel (vertices x)
  edge_label : ∀ e, LabelEquiv d (H.edgeLabel e) (P.edgeLabel (edges e))
  source : ∀ e, (H.source e).map (Port.map vertices) = P.source (edges e)
  target : ∀ e, (H.target e).map (Port.map vertices) = P.target (edges e)

namespace Realization
variable {d I O} {P : Presentation d I O} {H K : Hypernet d I O}

noncomputable def vertexBijection (a : Realization P H) (b : Realization P K) : Bijection H.Internal K.Internal :=
  Arithmetic.Reduction.sameRange a.vertices b.vertices a.vertex_injective b.vertex_injective
    (fun x => (a.vertex_range x).trans (b.vertex_range x).symm)
noncomputable def edgeBijection (a : Realization P H) (b : Realization P K) : Bijection H.Edge K.Edge :=
  Arithmetic.Reduction.sameRange a.edges b.edges a.edge_injective b.edge_injective
    (fun e => (a.edge_range e).trans (b.edge_range e).symm)

theorem vertex_commute (a : Realization P H) (b : Realization P K) (x) :
    b.vertices ((a.vertexBijection b).toFun x) = a.vertices x :=
  Arithmetic.Reduction.sameRange_commute a.vertices b.vertices a.vertex_injective b.vertex_injective _ x

theorem edge_commute (a : Realization P H) (b : Realization P K) (e) :
    b.edges ((a.edgeBijection b).toFun e) = a.edges e :=
  Arithmetic.Reduction.sameRange_commute a.edges b.edges a.edge_injective b.edge_injective _ e

theorem port_commute (a : Realization P H) (b : Realization P K) (v : H.Vertex) :
    Port.map b.vertices (Port.map (a.vertexBijection b).toFun v) = Port.map a.vertices v := by
  cases v <;> simp only [Port.map,vertex_commute]

/-- The common presentation determines the entire graph up to recursive isomorphism. -/
noncomputable def iso (a : Realization P H) (b : Realization P K) : DeepIso H K where
  vertices := a.vertexBijection b
  edges := a.edgeBijection b
  internal_label x := (b.internal_label _).trans ((congrArg P.vertexLabel (vertex_commute a b x)).trans (a.internal_label x).symm)
  edge_label e := by
    have hb := b.edge_label ((a.edgeBijection b).toFun e)
    rw [edge_commute] at hb
    exact labelEquiv_trans d (a.edge_label e) (labelEquiv_symm d hb)
  source e := by
    apply (List.map_inj_right (f := Port.map b.vertices) (fun _ _ h => Port.map_injective b.vertex_injective h)).mp
    rw [List.map_map]
    change (H.source e).map (fun v => Port.map b.vertices (Port.map (a.vertexBijection b).toFun v)) = _
    simp only [port_commute]
    rw [a.source,b.source,edge_commute]
  target e := by
    apply (List.map_inj_right (f := Port.map b.vertices) (fun _ _ h => Port.map_injective b.vertex_injective h)).mp
    rw [List.map_map]
    change (H.target e).map (fun v => Port.map b.vertices (Port.map (a.vertexBijection b).toFun v)) = _
    simp only [port_commute]
    rw [a.target,b.target,edge_commute]

noncomputable def stateIso (a : Realization P H) (b : Realization P K) {v : H.Vertex} {w : K.Vertex}
    (token : Port.map a.vertices v = Port.map b.vertices w) :
    Combined.StateIso ⟨H,(.search,v)⟩ ⟨K,(.search,w)⟩ where
  graph := a.iso b
  mode := rfl
  vertex := Port.map_injective b.vertex_injective ((port_commute a b v).trans token)

/-- Renaming the result graph does not change the presentation it realizes. -/
def rename (a : Realization P H) (f : DeepIso K H) : Realization P K where
  vertices := a.vertices ∘ f.vertices.toFun
  edges := a.edges ∘ f.edges.toFun
  vertex_injective := a.vertex_injective.comp (fun _ _ h => f.vertices.injective h)
  edge_injective := a.edge_injective.comp (fun _ _ h => f.edges.injective h)
  vertex_range x := by
    rw [← a.vertex_range]
    exact ⟨fun ⟨y,h⟩ => ⟨f.vertices.toFun y,h⟩,
      fun ⟨y,h⟩ => ⟨f.vertices.invFun y,by simpa [Function.comp_def,f.vertices.right_inv] using h⟩⟩
  edge_range e := by
    rw [← a.edge_range]
    exact ⟨fun ⟨y,h⟩ => ⟨f.edges.toFun y,h⟩,
      fun ⟨y,h⟩ => ⟨f.edges.invFun y,by simpa [Function.comp_def,f.edges.right_inv] using h⟩⟩
  internal_label x := (f.internal_label x).symm.trans (a.internal_label _)
  edge_label e := labelEquiv_trans d (f.edge_label e) (a.edge_label _)
  source e := by rw [Arithmetic.Reduction.map_ports_comp,f.source]; exact a.source _
  target e := by rw [Arithmetic.Reduction.map_ports_comp,f.target]; exact a.target _
end Realization
end Hypernets.Copying.Opening
