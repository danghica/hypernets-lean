import Hypernets.Copying.OpeningFiber

/-! Simultaneous expansion preserves the complete beta-opening certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.OpeningCertificate
open Graph Opening
variable {d I O k h} (C : Hypernet (d+1) I O)
    (F K : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e)
    {v w} {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : OpeningCertificate (F hole) (K hole) v w B)

def otherIso (e : C.Edge) (ne : e ≠ hole) : DeepIso (K e) (F e) :=
  Arithmetic.Reduction.equalIso (others e ne)

noncomputable def fiberVertices := Fiber.lift (fun e => (F e).Internal) (fun e => (K e).Internal)
  (openBody B).Internal hole a.realization.vertices (fun e ne => (otherIso C F K hole others e ne).vertices)
noncomputable def fiberEdges := Fiber.lift (fun e => (F e).Edge) (fun e => (K e).Edge)
  (openBody B).Edge hole a.realization.edges (fun e ne => (otherIso C F K hole others e ne).edges)
noncomputable def expansionVertices : (C.expand K).Internal → (a.matched.map (Occurrence.expand C F hole)).presentation.Vertex
  | .inl x => .inl (.inl x)
  | .inr x => shift (fiberVertices C F K hole others a x)
noncomputable def expansionEdges := fiberEdges C F K hole others a

theorem expansion_vertices_injective : Function.Injective (expansionVertices C F K hole others a) := by
  rintro (x | x) (y | y) eq
  · exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj eq))
  · exact False.elim (shift_not_host _ _ eq.symm)
  · exact False.elim (shift_not_host _ _ eq)
  · exact congrArg Sum.inr (Fiber.lift_injective _ _ _ _ _ _ a.realization.vertex_injective (shift_injective eq))
theorem expansion_edges_injective : Function.Injective (expansionEdges C F K hole others a) := by
  unfold expansionEdges fiberEdges
  exact Fiber.lift_injective _ _ _ _ _ _ a.realization.edge_injective

theorem expansion_vertex_range (x : (a.matched.map (Occurrence.expand C F hole)).presentation.Vertex) :
    (∃ y, expansionVertices C F K hole others a y = x) ↔
      (a.matched.map (Occurrence.expand C F hole)).presentation.keepVertex x := by
  classical
  rcases x with (x | ⟨e,x⟩) | x
  · simp [Sum.exists,expansionVertices,shift_not_host,Match.presentation,Match.map,Occurrence.expand]
  · simp only [Sum.exists,expansionVertices,Sum.inl.injEq,Sum.inl_ne_inr,shift_old]
    simp only [exists_false,false_or]
    by_cases eq : e = hole
    · subst e
      rw [show (∃ y, fiberVertices C F K hole others a y = .inl ⟨hole,x⟩) ↔
        ∃ y, a.realization.vertices y = .inl x from by unfold fiberVertices; exact Fiber.range_same (fun e => (F e).Internal) (fun e => (K e).Internal) (openBody B).Internal hole a.realization.vertices (fun e ne => (otherIso C F K hole others e ne).vertices) x,a.realization.vertex_range]
      simp [Match.map,Occurrence.expand]
    · have found := Fiber.range_other (fun e => (F e).Internal) (fun e => (K e).Internal)
        (openBody B).Internal hole a.realization.vertices (fun e ne => (otherIso C F K hole others e ne).vertices) eq x
      have ne (y : (F hole).Internal) : (⟨e,x⟩ : Σ e,(F e).Internal) ≠ ⟨hole,y⟩ := fun same => eq (congrArg Sigma.fst same)
      simp [fiberVertices,found,Match.presentation,Match.map,Occurrence.expand,ne]
  · simp only [Sum.exists,expansionVertices,Sum.inl_ne_inr,shift_new,exists_false,false_or]
    rw [show (∃ y, fiberVertices C F K hole others a y = .inr x) ↔
      ∃ y, a.realization.vertices y = .inr x from by unfold fiberVertices; exact Fiber.range_extra _ _ _ _ _ _ x,a.realization.vertex_range]

theorem expansion_edge_range (x : (a.matched.map (Occurrence.expand C F hole)).presentation.Edge) :
    (∃ y, expansionEdges C F K hole others a y = x) ↔
      (a.matched.map (Occurrence.expand C F hole)).presentation.keepEdge x := by
  classical
  rcases x with ⟨e,x⟩ | x
  · by_cases eq : e = hole
    · subst e
      change (∃ y, fiberEdges C F K hole others a y = .inl ⟨hole,x⟩) ↔ _
      rw [show (∃ y, fiberEdges C F K hole others a y = .inl ⟨hole,x⟩) ↔
        ∃ y, a.realization.edges y = .inl x from by unfold fiberEdges; exact Fiber.range_same (fun e => (F e).Edge) (fun e => (K e).Edge) (openBody B).Edge hole a.realization.edges (fun e ne => (otherIso C F K hole others e ne).edges) x,a.realization.edge_range]
      simp [Match.map,Occurrence.expand]
    · have found := Fiber.range_other (fun e => (F e).Edge) (fun e => (K e).Edge)
        (openBody B).Edge hole a.realization.edges (fun e ne => (otherIso C F K hole others e ne).edges) eq x
      have ne (y : (F hole).Edge) : (⟨e,x⟩ : Σ e,(F e).Edge) ≠ ⟨hole,y⟩ := fun same => eq (congrArg Sigma.fst same)
      simp [expansionEdges,fiberEdges,found,Match.presentation,Match.map,Occurrence.expand,ne]
  · change (∃ y, fiberEdges C F K hole others a y = .inr x) ↔ _
    rw [show (∃ y, fiberEdges C F K hole others a y = .inr x) ↔
      ∃ y, a.realization.edges y = .inr x from by unfold fiberEdges; exact Fiber.range_extra _ _ _ _ _ _ x,a.realization.edge_range]

theorem expansion_host_port (x : C.Vertex) :
    Port.map (expansionVertices C F K hole others a) (Net.Expansion.host C K x) =
      Port.map Sum.inl (Net.Expansion.host C F x) := by cases x <;> rfl

theorem expansion_selected_port (x : (K hole).Vertex) :
    Port.map (expansionVertices C F K hole others a) (Net.Expansion.insert C K hole x) =
      Match.originPort (B := B) (Occurrence.expand C F hole) (Port.map a.realization.vertices x) := by
  cases x with
  | internal x =>
    change Port.internal (shift (fiberVertices C F K hole others a ⟨hole,x⟩)) = _
    rw [fiberVertices,Fiber.lift_same]
    simp only [Port.map]
    cases a.realization.vertices x <;> rfl
  | input i => exact expansion_host_port C F K hole others a _
  | output i => exact expansion_host_port C F K hole others a _

theorem expansion_other_port {e} (ne : e ≠ hole) (x : (K e).Vertex) :
    Port.map (expansionVertices C F K hole others a) (Net.Expansion.insert C K e x) =
      Port.map Sum.inl (Net.Expansion.insert C F e (Port.map (otherIso C F K hole others e ne).vertices.toFun x)) := by
  cases x with
  | internal x =>
    change Port.internal (shift (fiberVertices C F K hole others a ⟨e,x⟩)) = _
    rw [fiberVertices,Fiber.lift_other _ _ _ _ _ _ ne]; rfl
  | input i => exact expansion_host_port C F K hole others a _
  | output i => exact expansion_host_port C F K hole others a _

theorem expansion_source (e : a.matched.presentation.Edge) :
    (a.matched.presentation.source e).map (Match.originPort (Occurrence.expand C F hole)) =
      (a.matched.map (Occurrence.expand C F hole)).presentation.source (Fiber.tag (fun e => (F e).Edge) (openBody B).Edge hole e) := by
  cases e with
  | inl e =>
    change ((F hole).source e |>.map (Port.map Sum.inl)).map _ = (((F hole).source e).map _).map _
    rw [List.map_map,List.map_map]
    exact List.map_congr_left (fun x _ => Match.origin_old _ x)
  | inr e =>
    change (((openBody B).source e).map a.matched.bodyPort).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => (a.matched.bodyPort_map _ x).symm)

theorem expansion_target (e : a.matched.presentation.Edge) :
    (a.matched.presentation.target e).map (Match.originPort (Occurrence.expand C F hole)) =
      (a.matched.map (Occurrence.expand C F hole)).presentation.target (Fiber.tag (fun e => (F e).Edge) (openBody B).Edge hole e) := by
  cases e with
  | inl e =>
    change ((F hole).target e |>.map (Port.map Sum.inl)).map _ = (((F hole).target e).map _).map _
    rw [List.map_map,List.map_map]
    exact List.map_congr_left (fun x _ => Match.origin_old _ x)
  | inr e =>
    change (((openBody B).target e).map a.matched.bodyPort).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => (a.matched.bodyPort_map _ x).symm)

noncomputable def expansionRealization :
    Realization (a.matched.map (Occurrence.expand C F hole)).presentation (C.expand K) where
  vertices := expansionVertices C F K hole others a
  edges := expansionEdges C F K hole others a
  vertex_injective := expansion_vertices_injective C F K hole others a
  edge_injective := expansion_edges_injective C F K hole others a
  vertex_range := expansion_vertex_range C F K hole others a
  edge_range := expansion_edge_range C F K hole others a
  internal_label := by
    rintro (x | ⟨e,x⟩)
    · rfl
    · by_cases eq : e = hole
      · subst e
        change (K hole).internalLabel x = _
        rw [a.realization.internal_label]
        change _ = (a.matched.map (Occurrence.expand C F hole)).presentation.vertexLabel
          (shift (fiberVertices C F K hole others a ⟨hole,x⟩))
        rw [fiberVertices,Fiber.lift_same]
        cases a.realization.vertices x <;> rfl
      · change (K e).internalLabel x = _
        change _ = (a.matched.map (Occurrence.expand C F hole)).presentation.vertexLabel
          (shift (fiberVertices C F K hole others a ⟨e,x⟩))
        rw [fiberVertices,Fiber.lift_other _ _ _ _ _ _ eq]
        exact (otherIso C F K hole others e eq).internal_label x |>.symm
  edge_label := by
    rintro ⟨e,x⟩
    by_cases eq : e = hole
    · subst e
      change LabelEquiv _ ((K hole).edgeLabel x) ((a.matched.map (Occurrence.expand C F hole)).presentation.edgeLabel (fiberEdges C F K hole others a ⟨hole,x⟩))
      rw [fiberEdges,Fiber.lift_same]
      have same : (a.matched.map (Occurrence.expand C F hole)).presentation.edgeLabel
          (Fiber.tag (fun e => (F e).Edge) (openBody B).Edge hole (a.realization.edges x)) =
          a.matched.presentation.edgeLabel (a.realization.edges x) := by cases a.realization.edges x <;> rfl
      rw [same]; exact a.realization.edge_label x
    · change LabelEquiv _ ((K e).edgeLabel x) ((a.matched.map (Occurrence.expand C F hole)).presentation.edgeLabel (fiberEdges C F K hole others a ⟨e,x⟩))
      rw [fiberEdges,Fiber.lift_other _ _ _ _ _ _ eq]
      exact (otherIso C F K hole others e eq).edge_label x
  source := by
    rintro ⟨e,x⟩
    change (((K e).source x).map (Net.Expansion.insert C K e)).map _ = (a.matched.map (Occurrence.expand C F hole)).presentation.source (fiberEdges C F K hole others a ⟨e,x⟩)
    by_cases eq : e = hole
    · subst e
      rw [fiberEdges,Fiber.lift_same,List.map_map]
      calc
        _ = (((K hole).source x).map (Port.map a.realization.vertices)).map (Match.originPort (Occurrence.expand C F hole)) := by
          rw [List.map_map]; exact List.map_congr_left (fun x _ => expansion_selected_port C F K hole others a x)
        _ = _ := by rw [a.realization.source]; exact expansion_source C F K hole a _
    · rw [fiberEdges,Fiber.lift_other _ _ _ _ _ _ eq]
      change (((K e).source x).map _).map _ = (((F e).source ((otherIso C F K hole others e eq).edges.toFun x)).map _).map _
      rw [← (otherIso C F K hole others e eq).source,List.map_map,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => expansion_other_port C F K hole others a eq x)
  target := by
    rintro ⟨e,x⟩
    change (((K e).target x).map (Net.Expansion.insert C K e)).map _ = (a.matched.map (Occurrence.expand C F hole)).presentation.target (fiberEdges C F K hole others a ⟨e,x⟩)
    by_cases eq : e = hole
    · subst e
      rw [fiberEdges,Fiber.lift_same,List.map_map]
      calc
        _ = (((K hole).target x).map (Port.map a.realization.vertices)).map (Match.originPort (Occurrence.expand C F hole)) := by
          rw [List.map_map]; exact List.map_congr_left (fun x _ => expansion_selected_port C F K hole others a x)
        _ = _ := by rw [a.realization.target]; exact expansion_target C F K hole a _
    · rw [fiberEdges,Fiber.lift_other _ _ _ _ _ _ eq]
      change (((K e).target x).map _).map _ = (((F e).target ((otherIso C F K hole others e eq).edges.toFun x)).map _).map _
      rw [← (otherIso C F K hole others e eq).target,List.map_map,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => expansion_other_port C F K hole others a eq x)

noncomputable def expand : OpeningCertificate (C.expand F) (C.expand K)
    (Net.Expansion.insert C F hole v) (Net.Expansion.insert C K hole w) B where
  matched := a.matched.map (Occurrence.expand C F hole)
  realization := expansionRealization C F K hole others a
  token := by
    rw [show (expansionRealization C F K hole others a).vertices = expansionVertices C F K hole others a from rfl,
      expansion_selected_port,a.token,Match.origin_old]
    rfl
end Hypernets.Copying.Application.OpeningCertificate
