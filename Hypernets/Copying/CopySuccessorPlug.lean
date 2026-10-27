import Hypernets.Copying.CopySuccessorOccurrence

/-! Complete copying certificates survive arbitrary typed plugging. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule.SuccessorCertificate
open Graph Opening
variable {d I O k h} (C : Hypernet d I O) (hole : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))}
    {v w} {B : Hypernet d [.term] (environmentInterface k h)}
    (a : SuccessorCertificate G H v w B)

def plugVertices : (C.plug hole H).Internal → (a.matched.map (Occurrence.plug C hole G)).presentation.Vertex
  | .inl x => .inl (.inl x)
  | .inr x => shift (a.realization.vertices x)

def plugEdges : (C.plug hole H).Edge → (a.matched.map (Occurrence.plug C hole G)).presentation.Edge
  | .inl e => .inl (.inl e)
  | .inr e => shift (a.realization.edges e)

theorem plug_vertices_injective : Function.Injective (plugVertices C hole a) := by
  rintro (x | x) (y | y) eq
  · exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj eq))
  · exact False.elim (shift_not_host _ _ eq.symm)
  · exact False.elim (shift_not_host _ _ eq)
  · exact congrArg Sum.inr (a.realization.vertex_injective (shift_injective eq))

theorem plug_edges_injective : Function.Injective (plugEdges C hole a) := by
  rintro (x | x) (y | y) eq
  · exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj eq))
  · exact False.elim (shift_not_host _ _ eq.symm)
  · exact False.elim (shift_not_host _ _ eq)
  · exact congrArg Sum.inr (a.realization.edge_injective (shift_injective eq))

theorem plug_vertex_range (x : (a.matched.map (Occurrence.plug C hole G)).presentation.Vertex) :
    (∃ y, plugVertices C hole a y = x) ↔ (a.matched.map (Occurrence.plug C hole G)).presentation.keepVertex x := by
  rcases x with (x | x) | x
  · simp [Sum.exists,plugVertices,shift_not_host,SuccessorMatch.presentation,SuccessorMatch.map,Occurrence.plug]
  · simp only [Sum.exists,plugVertices,Sum.inl.injEq,Sum.inl_ne_inr,shift_old,a.realization.vertex_range]
    simp
  · simp only [Sum.exists,plugVertices,Sum.inl_ne_inr,shift_new,a.realization.vertex_range]
    simp

theorem plug_edge_range (e : (a.matched.map (Occurrence.plug C hole G)).presentation.Edge) :
    (∃ f, plugEdges C hole a f = e) ↔ (a.matched.map (Occurrence.plug C hole G)).presentation.keepEdge e := by
  rcases e with (e | e) | e
  · simp [Sum.exists,plugEdges,shift_not_host,SuccessorMatch.presentation,SuccessorMatch.map,Occurrence.plug]
  · simp only [Sum.exists,plugEdges,Sum.inl.injEq,Sum.inl_ne_inr,shift_old,a.realization.edge_range]
    simp
  · simp only [Sum.exists,plugEdges,Sum.inl_ne_inr,shift_new,a.realization.edge_range]
    simp

theorem plug_host_port (x : C.Vertex) :
    Port.map (plugVertices C hole a) (Net.Replacement.host C hole H x) =
      Port.map Sum.inl (Net.Replacement.host C hole G x) := by cases x <;> rfl

theorem plug_component_port (x : H.Vertex) :
    Port.map (plugVertices C hole a) (Net.Replacement.insert C hole H x) =
      SuccessorMatch.originPort (H := B) (Occurrence.plug C hole G) (Port.map a.realization.vertices x) := by
  cases x with
  | internal x =>
    change Port.internal (shift (a.realization.vertices x)) = _
    change Port.internal (shift (a.realization.vertices x)) = SuccessorMatch.originPort (Occurrence.plug C hole G) (.internal (a.realization.vertices x))
    rcases a.realization.vertices x with x | (x | (x | (x | x))) <;> rfl
  | input i =>
    change Port.map _ (Net.Replacement.host C hole H (C.sourcePort hole i)) = _
    exact plug_host_port C hole a _
  | output i =>
    change Port.map _ (Net.Replacement.host C hole H (C.targetPort hole i)) = _
    exact plug_host_port C hole a _

theorem plug_source (e : a.matched.presentation.Edge) :
    (a.matched.presentation.source e).map (SuccessorMatch.originPort (Occurrence.plug C hole G)) =
      (a.matched.map (Occurrence.plug C hole G)).presentation.source (shift e) := by
  have same : SuccessorMatch.originEdge (H := B) (Occurrence.plug C hole G) e = shift e := by cases e <;> rfl
  rw [← same]; exact a.matched.source_map (Occurrence.plug C hole G) e

theorem plug_target (e : a.matched.presentation.Edge) :
    (a.matched.presentation.target e).map (SuccessorMatch.originPort (Occurrence.plug C hole G)) =
      (a.matched.map (Occurrence.plug C hole G)).presentation.target (shift e) := by
  have same : SuccessorMatch.originEdge (H := B) (Occurrence.plug C hole G) e = shift e := by cases e <;> rfl
  rw [← same]; exact a.matched.target_map (Occurrence.plug C hole G) e

/-- Every host occurrence survives; the selected component retains exactly its certified result. -/
noncomputable def plugRealization : Realization (a.matched.map (Occurrence.plug C hole G)).presentation (C.plug hole H) where
  vertices := plugVertices C hole a
  edges := plugEdges C hole a
  vertex_injective := plug_vertices_injective C hole a
  edge_injective := plug_edges_injective C hole a
  vertex_range := plug_vertex_range C hole a
  edge_range := plug_edge_range C hole a
  internal_label := by
    rintro (x | x)
    · rfl
    · change H.internalLabel x = _
      rw [a.realization.internal_label]
      change _ = (a.matched.map (Occurrence.plug C hole G)).presentation.vertexLabel (shift (a.realization.vertices x))
      rcases a.realization.vertices x with x | (x | (x | (x | x))) <;> rfl
  edge_label := by
    rintro (e | e)
    · exact labelEquiv_refl _ _
    · change LabelEquiv d (H.edgeLabel e)
        ((a.matched.map (Occurrence.plug C hole G)).presentation.edgeLabel (shift (a.realization.edges e)))
      have same : (a.matched.map (Occurrence.plug C hole G)).presentation.edgeLabel (shift (a.realization.edges e)) =
          a.matched.presentation.edgeLabel (a.realization.edges e) := by rcases a.realization.edges e with e | (e | (e | e)) <;> rfl
      rw [same]
      exact a.realization.edge_label e
  source := by
    rintro (e | e)
    · simp only [plugEdges,SuccessorMatch.presentation,SuccessorMatch.map,Occurrence.plug,Function.comp_apply,Sum.inl_ne_inr,↓reduceIte]
      change ((C.source e.val).map (Net.Replacement.host C hole H)).map _ = ((C.source e.val).map _).map _
      rw [List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => plug_host_port C hole a x)
    · change ((H.source e).map (Net.Replacement.insert C hole H)).map _ = _
      rw [List.map_map]
      calc
        _ = ((H.source e).map (Port.map a.realization.vertices)).map (SuccessorMatch.originPort (Occurrence.plug C hole G)) := by
          rw [List.map_map]; exact List.map_congr_left (fun x _ => plug_component_port C hole a x)
        _ = _ := by rw [a.realization.source]; exact plug_source C hole a _
  target := by
    rintro (e | e)
    · simp only [plugEdges,SuccessorMatch.presentation,SuccessorMatch.map,SuccessorMatch.tail,Occurrence.comp,Occurrence.plug,Function.comp_apply,Sum.inl_ne_inr,↓reduceIte]
      change ((C.target e.val).map (Net.Replacement.host C hole H)).map _ = ((C.target e.val).map _).map _
      rw [List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => plug_host_port C hole a x)
    · change ((H.target e).map (Net.Replacement.insert C hole H)).map _ = _
      rw [List.map_map]
      calc
        _ = ((H.target e).map (Port.map a.realization.vertices)).map (SuccessorMatch.originPort (Occurrence.plug C hole G)) := by
          rw [List.map_map]; exact List.map_congr_left (fun x _ => plug_component_port C hole a x)
        _ = _ := by rw [a.realization.target]; exact plug_target C hole a _

noncomputable def plug : SuccessorCertificate (C.plug hole G) (C.plug hole H)
    (Net.Replacement.insert C hole G v) (Net.Replacement.insert C hole H w) B where
  matched := a.matched.map (Occurrence.plug C hole G)
  realization := plugRealization C hole a
  token := by
    rw [show (plugRealization C hole a).vertices = plugVertices C hole a from rfl,
      plug_component_port,a.token,SuccessorMatch.origin_old]
    rfl
end Hypernets.Copying.CopyRule.SuccessorCertificate
