import Hypernets.Copying.CopySearchBarrier

/-! The complete copying certificate embeds every old source occurrence in its reduct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule.SuccessorCertificate
open Graph Opening
variable {d I O k h} {G K : Hypernet d I O} {v w}
    {H : Hypernet d [.term] (environmentInterface k h)} (a : SuccessorCertificate G K v w H)

noncomputable def retainedVertex (x : G.Internal) : K.Internal :=
  Classical.choose ((a.realization.vertex_range (.inl x)).mpr trivial)
noncomputable def retainedEdge (e : G.Edge) : K.Edge :=
  Classical.choose ((a.realization.edge_range (.inl e)).mpr trivial)
noncomputable def retainedPort : G.Vertex → K.Vertex := Port.map a.retainedVertex

theorem retained_vertex (x : G.Internal) : a.realization.vertices (a.retainedVertex x) = .inl x :=
  Classical.choose_spec ((a.realization.vertex_range (.inl x)).mpr trivial)
theorem retained_edge (e : G.Edge) : a.realization.edges (a.retainedEdge e) = .inl e :=
  Classical.choose_spec ((a.realization.edge_range (.inl e)).mpr trivial)
theorem retained_port (p : G.Vertex) : Port.map a.realization.vertices (a.retainedPort p) = Port.map Sum.inl p := by
  cases p <;> simp only [retainedPort,Port.map,retained_vertex]

theorem retained_port_injective : Function.Injective a.retainedPort := by
  intro p q eq
  exact Port.map_injective (f := fun x : G.Internal => (Sum.inl x : G.Internal ⊕ AddedVertex H)) (fun _ _ h => Sum.inl.inj h) ((a.retained_port p).symm.trans ((congrArg (Port.map a.realization.vertices) eq).trans (a.retained_port q)))

theorem retained_label (e : G.Edge) (p : Primitive) (label : G.edgeLabel e = primitiveLabel d p) :
    K.edgeLabel (a.retainedEdge e) = primitiveLabel d p := by
  have rel := a.realization.edge_label (a.retainedEdge e)
  rw [retained_edge] at rel
  exact (Search.primitive_equiv rel p).mpr label

theorem retained_source (e : G.Edge) (ne : e ≠ a.matched.active) :
    (G.source e).map a.retainedPort = K.source (a.retainedEdge e) := by
  apply (List.map_inj_right (f := Port.map a.realization.vertices)
    (fun _ _ h => Port.map_injective a.realization.vertex_injective h)).mp
  rw [List.map_map,a.realization.source,retained_edge]
  simp only [SuccessorMatch.presentation,ite_eq_right ne]
  exact List.map_congr_left (fun p _ => a.retained_port p)

theorem retained_target (e : G.Edge) (ne : e ≠ a.matched.tail) :
    (G.target e).map a.retainedPort = K.target (a.retainedEdge e) := by
  apply (List.map_inj_right (f := Port.map a.realization.vertices)
    (fun _ _ h => Port.map_injective a.realization.vertex_injective h)).mp
  rw [List.map_map,a.realization.target,retained_edge]
  simp only [SuccessorMatch.presentation,ite_eq_right ne]
  exact List.map_congr_left (fun p _ => a.retained_port p)

theorem retained_token : a.retainedPort v = w :=
  Port.map_injective a.realization.vertex_injective ((a.retained_port v).trans a.token.symm)
end Hypernets.Copying.CopyRule.SuccessorCertificate
