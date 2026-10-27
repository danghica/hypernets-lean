import Hypernets.Copying.OpeningOccurrence

/-! Carrier changes of a partial presentation preserve its complete realizations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening
open Graph

structure Presentation.Iso {d I O} (P Q : Presentation d I O) where
  vertices : Bijection P.Vertex Q.Vertex
  edges : Bijection P.Edge Q.Edge
  vertex_range : ∀ x, Q.keepVertex (vertices.toFun x) ↔ P.keepVertex x
  edge_range : ∀ e, Q.keepEdge (edges.toFun e) ↔ P.keepEdge e
  vertex_label : ∀ x, Q.vertexLabel (vertices.toFun x) = P.vertexLabel x
  edge_label : ∀ e, LabelEquiv d (P.edgeLabel e) (Q.edgeLabel (edges.toFun e))
  source : ∀ e, (P.source e).map (Port.map vertices.toFun) = Q.source (edges.toFun e)
  target : ∀ e, (P.target e).map (Port.map vertices.toFun) = Q.target (edges.toFun e)

/-- Reindex the common occurrence space without changing the realized graph. -/
def Realization.transport {d I O} {P Q : Presentation d I O} {H : Hypernet d I O}
    (a : Realization P H) (f : P.Iso Q) : Realization Q H where
  vertices := f.vertices.toFun ∘ a.vertices
  edges := f.edges.toFun ∘ a.edges
  vertex_injective := fun _ _ h => a.vertex_injective (f.vertices.injective h)
  edge_injective := fun _ _ h => a.edge_injective (f.edges.injective h)
  vertex_range x := by
    have same := f.vertex_range (f.vertices.invFun x)
    rw [f.vertices.right_inv,← a.vertex_range] at same
    rw [same]
    exact ⟨fun ⟨y,hy⟩ => ⟨y,by rw [← hy]; exact (f.vertices.left_inv _).symm⟩,
      fun ⟨y,hy⟩ => ⟨y,by change f.vertices.toFun (a.vertices y) = x; rw [hy,f.vertices.right_inv]⟩⟩
  edge_range e := by
    have same := f.edge_range (f.edges.invFun e)
    rw [f.edges.right_inv,← a.edge_range] at same
    rw [same]
    exact ⟨fun ⟨y,hy⟩ => ⟨y,by rw [← hy]; exact (f.edges.left_inv _).symm⟩,
      fun ⟨y,hy⟩ => ⟨y,by change f.edges.toFun (a.edges y) = e; rw [hy,f.edges.right_inv]⟩⟩
  internal_label x := (a.internal_label x).trans (f.vertex_label _).symm
  edge_label e := labelEquiv_trans d (a.edge_label e) (f.edge_label _)
  source e := by rw [Arithmetic.Reduction.map_ports_comp,a.source,f.source]; rfl
  target e := by rw [Arithmetic.Reduction.map_ports_comp,a.target,f.target]; rfl
end Hypernets.Copying.Opening

namespace Hypernets.Copying.Application.Match
open Graph Opening
variable {d I O k h} {G H : Hypernet (d+1) I O} {v}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}

theorem origin_iso (f : DeepIso G H) (x : Port (G.Internal ⊕ (openBody B).Internal) I.length O.length) :
    originPort (B := B) (Occurrence.ofIso f) x = Port.map (f.vertices.sum (Bijection.refl _)).toFun x := by
  cases x with
  | internal x => cases x <;> rfl
  | input i => rfl
  | output i => rfl

/-- Recursive source renaming preserves both old and newly exposed occurrences. -/
def renamePresentation (a : Match G v B) (f : DeepIso G H) :
    a.presentation.Iso (a.map (Occurrence.ofIso f)).presentation where
  vertices := f.vertices.sum (Bijection.refl _)
  edges := f.edges.sum (Bijection.refl _)
  vertex_range := by
    rintro (x | x)
    · change (_ ≠ _ ∧ _ ≠ _) ↔ _
      constructor
      · intro hx; exact ⟨fun h => hx.1 (congrArg f.vertices.toFun h),fun h => hx.2 (congrArg f.vertices.toFun h)⟩
      · intro hx; exact ⟨fun h => hx.1 (f.vertices.injective h),fun h => hx.2 (f.vertices.injective h)⟩
    · rfl
  edge_range := by
    rintro (e | e)
    · change (_ ≠ _ ∧ _ ≠ _ ∧ _ ≠ _) ↔ _
      constructor
      · intro he; exact ⟨fun h => he.1 (congrArg f.edges.toFun h),fun h => he.2.1 (congrArg f.edges.toFun h),fun h => he.2.2 (congrArg f.edges.toFun h)⟩
      · intro he; exact ⟨fun h => he.1 (f.edges.injective h),fun h => he.2.1 (f.edges.injective h),fun h => he.2.2 (f.edges.injective h)⟩
    · rfl
  vertex_label := by rintro (x | x); exact f.internal_label x; rfl
  edge_label := by rintro (e | e); exact f.edge_label e; exact labelEquiv_refl _ _
  source := by
    rintro (e | e)
    · change ((G.source e).map (Port.map Sum.inl)).map _ = (H.source _).map _
      rw [← f.source,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => by cases x <;> rfl)
    · change (((openBody B).source e).map a.bodyPort).map _ = _
      rw [List.map_map]
      apply List.map_congr_left
      intro x _
      rw [bodyPort_map,origin_iso]
      rfl
  target := by
    rintro (e | e)
    · change ((G.target e).map (Port.map Sum.inl)).map _ = (H.target _).map _
      rw [← f.target,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => by cases x <;> rfl)
    · change (((openBody B).target e).map a.bodyPort).map _ = _
      rw [List.map_map]
      apply List.map_congr_left
      intro x _
      rw [bodyPort_map,origin_iso]
      rfl

/-- Common source wiring transports the opened-body attachment through its recursive isomorphism. -/
theorem bodyPort_congr (a : Match G v B) (b : Match G v C) (f : DeepIso (openBody B) (openBody C))
    (x : (openBody B).Vertex) :
    Port.map ((Bijection.refl G.Internal).sum f.vertices).toFun (a.bodyPort x) =
      b.bodyPort (Port.map f.vertices.toFun x) := by
  obtain ⟨_,_,boxEq,_,_,argEq⟩ := shape_unique a b
  cases x with
  | internal x => rfl
  | input i => cases v <;> rfl
  | output i =>
    simp only [bodyPort,Port.map,Bijection.sum,Bijection.refl,argEq,boxEq]
    cases (b.argumentPort :: G.target b.boxEdge)[i.val]'(by rw [b.output_length]; exact i.isLt) <;> rfl

/-- Two independently represented bodies yield isomorphic complete opening presentations. -/
def bodyPresentation (a : Match G v B) (b : Match G v C) (f : DeepIso (openBody B) (openBody C)) :
    a.presentation.Iso b.presentation where
  vertices := (Bijection.refl G.Internal).sum f.vertices
  edges := (Bijection.refl G.Edge).sum f.edges
  vertex_range := by
    obtain ⟨_,_,_,funEq,thunkEq,_⟩ := shape_unique a b
    rintro (x | x)
    · change (x ≠ b.functionWire ∧ x ≠ b.thunkWire) ↔ _
      rw [← funEq,← thunkEq]
    · rfl
  edge_range := by
    obtain ⟨appEq,lamEq,boxEq,_⟩ := shape_unique a b
    rintro (e | e)
    · change (e ≠ b.app ∧ e ≠ b.lam ∧ e ≠ b.boxEdge) ↔ _
      rw [← appEq,← lamEq,← boxEq]
    · rfl
  vertex_label := by rintro (x | x); rfl; exact f.internal_label x
  edge_label := by rintro (e | e); exact labelEquiv_refl _ _; exact f.edge_label e
  source := by
    rintro (e | e)
    · change ((G.source e).map (Port.map Sum.inl)).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => by cases x <;> rfl)
    · change (((openBody B).source e).map a.bodyPort).map _ = ((openBody C).source _).map b.bodyPort
      rw [← f.source,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => bodyPort_congr a b f x)
  target := by
    rintro (e | e)
    · change ((G.target e).map (Port.map Sum.inl)).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => by cases x <;> rfl)
    · change (((openBody B).target e).map a.bodyPort).map _ = ((openBody C).target _).map b.bodyPort
      rw [← f.target,List.map_map,List.map_map]
      exact List.map_congr_left (fun x _ => bodyPort_congr a b f x)
end Hypernets.Copying.Application.Match
