import Hypernets.Copying.DereferenceCoherenceExamples

/-! Source-relative certificates for arithmetic deletion. The operational rules are unchanged. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph

/-- The numeric operand wires are internal, so a reduction cannot delete a host boundary. -/
def InternalTargets {d I O} (G : Hypernet d I O) (e : G.Edge) : Prop :=
  ∀ v ∈ G.target e, ∃ x, v = .internal x

/-- A certificate identifies every surviving carrier with its original occurrence.
Only the head changes label and loses its targets; its immediate operands are removed. -/
structure Reduction {d I O} (G H : Hypernet d I O) (head : G.Edge) (result : Nat) where
  vertices : H.Internal → G.Internal
  vertex_injective : Function.Injective vertices
  vertex_range : ∀ x, (∃ y, vertices y = x) ↔ Port.internal x ∉ G.target head
  edges : H.Edge → G.Edge
  edge_injective : Function.Injective edges
  edge_range : ∀ e, (∃ f, edges f = e) ↔ ¬ G.Adjacent head e
  internal_label : ∀ x, H.internalLabel x = G.internalLabel (vertices x)
  edge_head : ∀ e, edges e = head → H.edgeLabel e = primitiveLabel d (.operation (.const (.nat result)))
  edge_other : ∀ e, edges e ≠ head → LabelEquiv d (H.edgeLabel e) (G.edgeLabel (edges e))
  source : ∀ e, (H.source e).map (Port.map vertices) = G.source (edges e)
  target_head : ∀ e, edges e = head → H.target e = []
  target_other : ∀ e, edges e ≠ head → (H.target e).map (Port.map vertices) = G.target (edges e)

namespace Reduction
variable {d I O} {G H K : Hypernet d I O} {head : G.Edge} {result : Nat}

/-- Two injective maps with the same image induce a bijection of their domains. -/
noncomputable def sameRange {A B C : Type} (f : A → C) (g : B → C)
    (fi : Function.Injective f) (gi : Function.Injective g)
    (range : ∀ c, (∃ a, f a = c) ↔ ∃ b, g b = c) : Bijection A B where
  toFun a := Classical.choose ((range (f a)).mp ⟨a,rfl⟩)
  invFun b := Classical.choose ((range (g b)).mpr ⟨b,rfl⟩)
  left_inv a := fi ((Classical.choose_spec ((range _).mpr ⟨_,rfl⟩)).trans
    (Classical.choose_spec ((range _).mp ⟨a,rfl⟩)))
  right_inv b := gi ((Classical.choose_spec ((range _).mp ⟨_,rfl⟩)).trans
    (Classical.choose_spec ((range _).mpr ⟨b,rfl⟩)))

theorem sameRange_commute {A B C : Type} (f : A → C) (g : B → C)
    (fi : Function.Injective f) (gi : Function.Injective g)
    (range : ∀ c, (∃ a, f a = c) ↔ ∃ b, g b = c) (a : A) :
    g ((sameRange f g fi gi range).toFun a) = f a := Classical.choose_spec ((range (f a)).mp ⟨a,rfl⟩)

noncomputable def vertexBijection (a : Reduction G H head result) (b : Reduction G K head result) :
    Bijection H.Internal K.Internal :=
  sameRange a.vertices b.vertices a.vertex_injective b.vertex_injective
    (fun x => (a.vertex_range x).trans (b.vertex_range x).symm)

noncomputable def edgeBijection (a : Reduction G H head result) (b : Reduction G K head result) :
    Bijection H.Edge K.Edge :=
  sameRange a.edges b.edges a.edge_injective b.edge_injective
    (fun e => (a.edge_range e).trans (b.edge_range e).symm)

theorem vertex_commute (a : Reduction G H head result) (b : Reduction G K head result) (x) :
    b.vertices ((vertexBijection a b).toFun x) = a.vertices x := sameRange_commute a.vertices b.vertices a.vertex_injective b.vertex_injective _ x

theorem edge_commute (a : Reduction G H head result) (b : Reduction G K head result) (e) :
    b.edges ((edgeBijection a b).toFun e) = a.edges e := sameRange_commute a.edges b.edges a.edge_injective b.edge_injective _ e

theorem port_commute (a : Reduction G H head result) (b : Reduction G K head result) (v : H.Vertex) :
    Port.map b.vertices (Port.map (vertexBijection a b).toFun v) = Port.map a.vertices v := by
  cases v <;> simp only [Port.map,vertex_commute]

/-- Equal source-relative deletion certificates compare whole graphs, including nested labels. -/
noncomputable def iso (a : Reduction G H head result) (b : Reduction G K head result) : DeepIso H K where
  vertices := vertexBijection a b
  edges := edgeBijection a b
  internal_label x := (b.internal_label _).trans ((congrArg G.internalLabel (vertex_commute a b x)).trans (a.internal_label x).symm)
  edge_label e := by
    by_cases eq : a.edges e = head
    · rw [a.edge_head e eq,b.edge_head _ ((edge_commute a b e).trans eq)]
      exact labelEquiv_refl d _
    · have hb := b.edge_other ((edgeBijection a b).toFun e) (by rw [edge_commute]; exact eq)
      rw [edge_commute] at hb
      exact labelEquiv_trans d (a.edge_other e eq) (labelEquiv_symm d hb)
  source e := by
    apply (List.map_inj_right (f := Port.map b.vertices) (fun _ _ h => Port.map_injective b.vertex_injective h)).mp
    rw [List.map_map]
    change (H.source e).map (fun v => Port.map b.vertices (Port.map (vertexBijection a b).toFun v)) = _
    simp only [port_commute]
    rw [a.source,b.source,edge_commute]
  target e := by
    apply (List.map_inj_right (f := Port.map b.vertices) (fun _ _ h => Port.map_injective b.vertex_injective h)).mp
    rw [List.map_map]
    change (H.target e).map (fun v => Port.map b.vertices (Port.map (vertexBijection a b).toFun v)) = _
    simp only [port_commute]
    by_cases eq : a.edges e = head
    · rw [a.target_head e eq,b.target_head _ ((edge_commute a b e).trans eq)]
      rfl
    · rw [a.target_other e eq,b.target_other _ (by rw [edge_commute]; exact eq),edge_commute]

/-- If both retained tokens denote the same original port, the complete states agree. -/
noncomputable def stateIso (a : Reduction G H head result) (b : Reduction G K head result)
    {v : H.Vertex} {w : K.Vertex} (token : Port.map a.vertices v = Port.map b.vertices w) :
    Combined.StateIso ⟨H,(.search,v)⟩ ⟨K,(.search,w)⟩ where
  graph := iso a b
  mode := rfl
  vertex := Port.map_injective b.vertex_injective ((port_commute a b v).trans token)
end Reduction
end Hypernets.Copying.Arithmetic
