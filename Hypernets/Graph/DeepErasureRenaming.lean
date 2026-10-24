import Hypernets.Graph.DeepInsertionRenaming

/-! Erasure commutes with recursive focus-preserving renaming. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}
    {G H : Hypernet ops d I []} {f : Focussed G} {g : Focussed H}

namespace Focussed.DeepIso
variable (a : DeepIso f g)

/-- The internal target selected by erasure is carried to the selected target. -/
theorem targetVertex : a.graph.vertices.toFun f.targetVertex = g.targetVertex := by
  have h := a.target
  rw [f.targetVertex_spec, g.targetVertex_spec] at h
  exact Port.internal.inj h

/-- The induced bijection on the undeleted internal vertices. -/
noncomputable def erasedVertices : Bijection f.underlying.Internal g.underlying.Internal :=
  exceptOfEq a.graph.vertices f.targetVertex g.targetVertex a.targetVertex

/-- The induced bijection on the non-focus edges. -/
def erasedEdges : Bijection f.underlying.Edge g.underlying.Edge :=
  exceptOfEq a.graph.edges f.edge g.edge a.focus

theorem erased_lift (v : f.underlying.Vertex) :
    FocusErasure.lift g.targetVertex (Port.map a.erasedVertices.toFun v) =
      Port.map a.graph.vertices.toFun (FocusErasure.lift f.targetVertex v) := by
  cases v <;> rfl

/-- The joined source vertex is natural under focus-preserving renaming. -/
theorem erased_position :
    Port.map a.erasedVertices.toFun
      (FocusErasure.position f f.targetVertex f.targetVertex_spec) =
      FocusErasure.position g g.targetVertex g.targetVertex_spec := by
  apply FocusErasure.lift_injective g.targetVertex
  rw [erased_lift, FocusErasure.lift_position, FocusErasure.lift_position, a.source]

/-- Contraction commutes with the induced renaming on retained vertices. -/
theorem erased_contract (v : G.Vertex) :
    Port.map a.erasedVertices.toFun (FocusErasure.contract f f.targetVertex f.targetVertex_spec v) =
      FocusErasure.contract g g.targetVertex g.targetVertex_spec (Port.map a.graph.vertices.toFun v) := by
  classical
  by_cases h : v = .internal f.targetVertex
  · subst v
    have ht : Port.map a.graph.vertices.toFun (.internal f.targetVertex : G.Vertex) = .internal g.targetVertex :=
      congrArg Port.internal a.targetVertex
    rw [ht, FocusErasure.contract_target, FocusErasure.contract_target, erased_position]
  · have ne : Port.map a.graph.vertices.toFun v ≠ .internal g.targetVertex := by
      intro eq
      apply h
      apply (Port.bijection a.graph.vertices).injective
      exact eq.trans (congrArg Port.internal a.targetVertex).symm
    apply FocusErasure.lift_injective g.targetVertex
    rw [erased_lift, FocusErasure.lift_contract _ _ _ _ h, FocusErasure.lift_contract _ _ _ _ ne]

/-- An actual isomorphism of the erased graphs, including ordered incidences. -/
noncomputable def erased : Linear.DeepIso f.underlying g.underlying where
  vertices := a.erasedVertices
  edges := a.erasedEdges
  internal_label v := a.graph.internal_label v.val
  edge_label e := a.graph.edge_label e.val
  source := by
    intro e
    change ((G.source e.val).map _).map _ =
      (H.source (a.graph.edges.toFun e.val)).map _
    rw [← a.graph.source, List.map_map, List.map_map]
    apply List.map_congr_left
    intro v _
    exact a.erased_contract v
  target := by
    intro e
    change ((G.target e.val).map _).map _ =
      (H.target (a.graph.edges.toFun e.val)).map _
    rw [← a.graph.target, List.map_map, List.map_map]
    apply List.map_congr_left
    intro v _
    exact a.erased_contract v

end Focussed.DeepIso

end Hypernets.Linear
