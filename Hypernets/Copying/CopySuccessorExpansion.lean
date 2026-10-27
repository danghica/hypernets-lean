import Hypernets.Copying.CopySuccessorComparison

/-! Simultaneous expansion preserves the complete copying-successor certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Fiber
open Graph
theorem surjective {E : Type} (F K : E → Type) (extra : Type) (hole : E)
    (selected : K hole → F hole ⊕ extra) (other : ∀ e, e ≠ hole → Bijection (K e) (F e))
    (surj : Function.Surjective selected) : Function.Surjective (lift F K extra hole selected other) := by
  classical
  rintro (⟨e,x⟩ | x)
  · by_cases eq : e = hole
    · subst e; exact (range_same F K extra hole selected other x).mpr (surj (.inl x))
    · exact range_other F K extra hole selected other eq x
  · exact (range_extra F K extra hole selected other x).mpr (surj (.inr x))
end Hypernets.Copying.Opening.Fiber

namespace Hypernets.Copying.CopyRule.SuccessorCertificate
open Graph Opening
variable {d I O k h} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e)
    {v w} {B : Hypernet d [.term] (environmentInterface k h)}
    (a : SuccessorCertificate (F hole) (K hole) v w B)

def otherIso (e : C.Edge) (ne : e ≠ hole) : DeepIso (K e) (F e) :=
  Arithmetic.Reduction.equalIso (others e ne)

noncomputable def fiberVertices := Fiber.lift (fun e => (F e).Internal) (fun e => (K e).Internal)
  (AddedVertex B) hole a.realization.vertices (fun e ne => (otherIso C F K hole others e ne).vertices)
noncomputable def fiberEdges := Fiber.lift (fun e => (F e).Edge) (fun e => (K e).Edge)
  (AddedEdge B) hole a.realization.edges (fun e ne => (otherIso C F K hole others e ne).edges)
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
  have surj : Function.Surjective (fiberVertices C F K hole others a) :=
    Fiber.surjective _ _ _ _ _ _ (fun x => (a.realization.vertex_range x).mpr trivial)
  constructor
  · intro _; trivial
  · intro _
    rcases x with (x | x) | x
    · exact ⟨.inl x,rfl⟩
    · obtain ⟨y,hy⟩ := surj (.inl x)
      exact ⟨.inr y,by change shift (fiberVertices C F K hole others a y) = _;rw [hy];rfl⟩
    · obtain ⟨y,hy⟩ := surj (.inr x)
      exact ⟨.inr y,by change shift (fiberVertices C F K hole others a y) = _;rw [hy];rfl⟩

theorem expansion_edge_range (x : (a.matched.map (Occurrence.expand C F hole)).presentation.Edge) :
    (∃ y, expansionEdges C F K hole others a y = x) ↔
      (a.matched.map (Occurrence.expand C F hole)).presentation.keepEdge x := by
  constructor
  · intro _; trivial
  · intro _
    unfold expansionEdges fiberEdges
    exact Fiber.surjective _ _ _ _ _ _ (fun x => (a.realization.edge_range x).mpr trivial) x

theorem expansion_host_port (x : C.Vertex) :
    Port.map (expansionVertices C F K hole others a) (Net.Expansion.host C K x) =
      Port.map Sum.inl (Net.Expansion.host C F x) := by cases x <;> rfl

theorem expansion_selected_port (x : (K hole).Vertex) :
    Port.map (expansionVertices C F K hole others a) (Net.Expansion.insert C K hole x) =
      SuccessorMatch.originPort (H := B) (Occurrence.expand C F hole) (Port.map a.realization.vertices x) := by
  cases x with
  | internal x =>
    change Port.internal (shift (fiberVertices C F K hole others a ⟨hole,x⟩)) = _
    rw [fiberVertices,Fiber.lift_same]
    simp only [Port.map]
    rcases a.realization.vertices x with x | (x | (x | (x | x))) <;> rfl
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
    (a.matched.presentation.source e).map (SuccessorMatch.originPort (Occurrence.expand C F hole)) =
      (a.matched.map (Occurrence.expand C F hole)).presentation.source
        (Fiber.tag (fun e => (F e).Edge) (AddedEdge B) hole e) := by
  have same : SuccessorMatch.originEdge (H := B) (Occurrence.expand C F hole) e = Fiber.tag (fun e => (F e).Edge) (AddedEdge B) hole e := by cases e <;> rfl
  rw [← same]; exact a.matched.source_map (Occurrence.expand C F hole) e

theorem expansion_target (e : a.matched.presentation.Edge) :
    (a.matched.presentation.target e).map (SuccessorMatch.originPort (Occurrence.expand C F hole)) =
      (a.matched.map (Occurrence.expand C F hole)).presentation.target
        (Fiber.tag (fun e => (F e).Edge) (AddedEdge B) hole e) := by
  have same : SuccessorMatch.originEdge (H := B) (Occurrence.expand C F hole) e = Fiber.tag (fun e => (F e).Edge) (AddedEdge B) hole e := by cases e <;> rfl
  rw [← same]; exact a.matched.target_map (Occurrence.expand C F hole) e

theorem outside_source {e} (ne : e ≠ hole) (x : (F e).Edge) :
    (a.matched.map (Occurrence.expand C F hole)).presentation.source (.inl ⟨e,x⟩) =
      (((F e).source x).map (Net.Expansion.insert C F e)).map (Port.map Sum.inl) := by
  classical
  simp only [SuccessorMatch.presentation,SuccessorMatch.map,Occurrence.expand]
  rw [ite_eq_right (fun eq => ne (congrArg Sigma.fst eq))]
  rfl

theorem outside_target {e} (ne : e ≠ hole) (x : (F e).Edge) :
    (a.matched.map (Occurrence.expand C F hole)).presentation.target (.inl ⟨e,x⟩) =
      (((F e).target x).map (Net.Expansion.insert C F e)).map (Port.map Sum.inl) := by
  classical
  simp only [SuccessorMatch.presentation,SuccessorMatch.map,SuccessorMatch.tail,Occurrence.comp,Occurrence.expand,Function.comp_apply]
  rw [ite_eq_right (fun eq => ne (congrArg Sigma.fst eq))]
  rfl

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
        rcases a.realization.vertices x with x | (x | (x | (x | x))) <;> rfl
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
          (Fiber.tag (fun e => (F e).Edge) (AddedEdge B) hole (a.realization.edges x)) =
          a.matched.presentation.edgeLabel (a.realization.edges x) := by rcases a.realization.edges x with x | (x | (x | x)) <;> rfl
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
        _ = (((K hole).source x).map (Port.map a.realization.vertices)).map (SuccessorMatch.originPort (Occurrence.expand C F hole)) := by
          rw [List.map_map]; exact List.map_congr_left (fun x _ => expansion_selected_port C F K hole others a x)
        _ = _ := by rw [a.realization.source]; exact expansion_source C F K hole a _
    · rw [fiberEdges,Fiber.lift_other _ _ _ _ _ _ eq]
      rw [outside_source C F K hole a eq]
      rw [← (otherIso C F K hole others e eq).source,List.map_map,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => expansion_other_port C F K hole others a eq x)
  target := by
    rintro ⟨e,x⟩
    change (((K e).target x).map (Net.Expansion.insert C K e)).map _ = (a.matched.map (Occurrence.expand C F hole)).presentation.target (fiberEdges C F K hole others a ⟨e,x⟩)
    by_cases eq : e = hole
    · subst e
      rw [fiberEdges,Fiber.lift_same,List.map_map]
      calc
        _ = (((K hole).target x).map (Port.map a.realization.vertices)).map (SuccessorMatch.originPort (Occurrence.expand C F hole)) := by
          rw [List.map_map]; exact List.map_congr_left (fun x _ => expansion_selected_port C F K hole others a x)
        _ = _ := by rw [a.realization.target]; exact expansion_target C F K hole a _
    · rw [fiberEdges,Fiber.lift_other _ _ _ _ _ _ eq]
      rw [outside_target C F K hole a eq]
      rw [← (otherIso C F K hole others e eq).target,List.map_map,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => expansion_other_port C F K hole others a eq x)

noncomputable def expand : SuccessorCertificate (C.expand F) (C.expand K)
    (Net.Expansion.insert C F hole v) (Net.Expansion.insert C K hole w) B where
  matched := a.matched.map (Occurrence.expand C F hole)
  realization := expansionRealization C F K hole others a
  token := by
    rw [show (expansionRealization C F K hole others a).vertices = expansionVertices C F K hole others a from rfl,
      expansion_selected_port,a.token,SuccessorMatch.origin_old]
    rfl
end Hypernets.Copying.CopyRule.SuccessorCertificate
