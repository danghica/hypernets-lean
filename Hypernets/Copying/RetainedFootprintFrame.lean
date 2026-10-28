import Hypernets.Copying.RetainedFootprintNormalisation
import Hypernets.Copying.CompleteMatchRealization
import Hypernets.Graph.ExpansionTransport

/-! Group a complete retained footprint into one selected component, while
every unrelated original filling remains an independent component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding)

noncomputable def frame : Hypernet d I O :=
  CompleteMatchCut.net (skeletonOccurrence C f cert avoid).matchEmbedding
    (skeletonOccurrence C f cert avoid).label

variable (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
  ((alphabet d).signature.output (C.edgeLabel e)))

noncomputable def localFamily (e : (skeleton C f cert avoid).Edge) := F (f.edges e).1

noncomputable def grouped (e : (frame C f cert avoid).Edge) : Hypernet d
    ((alphabet d).signature.input ((frame C f cert avoid).edgeLabel e))
    ((alphabet d).signature.output ((frame C f cert avoid).edgeLabel e)) :=
  match e with
  | none => ((skeleton C f cert avoid).expand (localFamily C f cert avoid F)).reboundary
      (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
  | some e => F e.val

noncomputable def frameEdgePartition : Bijection
    (CompleteMatchCut.RetainedEdge (skeletonOccurrence C f cert avoid).matchEmbedding ⊕ A.Edge) C.Edge :=
  Bijection.ofComplement (fun e => (f.edges e).1) (owner_injective C f.matchEmbedding cert avoid)

/-- Regroup only the carrier tags; no vertex is created or discarded. -/
noncomputable def frameVertexSplit : Bijection
    ((frame C f cert avoid).expand (grouped C f cert avoid F)).Internal
    ((CompleteMatchCut.Internal (skeletonOccurrence C f cert avoid).matchEmbedding ⊕ A.Internal) ⊕
      (Σ e, (F ((frameEdgePartition C f cert avoid).toFun e)).Internal)) where
  toFun
    | .inl v => .inl (.inl v)
    | .inr ⟨none,.inl v⟩ => .inl (.inr v)
    | .inr ⟨none,.inr ⟨e,v⟩⟩ => .inr ⟨.inr e,v⟩
    | .inr ⟨some e,v⟩ => .inr ⟨.inl e,v⟩
  invFun
    | .inl (.inl v) => .inl v
    | .inl (.inr v) => .inr ⟨none,.inl v⟩
    | .inr ⟨.inl e,v⟩ => .inr ⟨some e,v⟩
    | .inr ⟨.inr e,v⟩ => .inr ⟨none,.inr ⟨e,v⟩⟩
  left_inv v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · cases e with
      | none => rcases v with v | ⟨e,v⟩ <;> rfl
      | some e => rfl
  right_inv v := by rcases v with (v | v) | ⟨e | e,v⟩ <;> rfl

noncomputable def frameVertices : Bijection
    ((frame C f cert avoid).expand (grouped C f cert avoid F)).Internal (C.expand F).Internal :=
  (frameVertexSplit C f cert avoid F).trans
    ((CompleteMatchCut.vertices (skeletonOccurrence C f cert avoid).matchEmbedding).sum
      (Bijection.sigmaMap (frameEdgePartition C f cert avoid) (fun _ => Bijection.refl _)))

noncomputable def frameEdgeSplit : Bijection
    ((frame C f cert avoid).expand (grouped C f cert avoid F)).Edge
    (Σ e, (F ((frameEdgePartition C f cert avoid).toFun e)).Edge) where
  toFun
    | ⟨none,⟨e,x⟩⟩ => ⟨.inr e,x⟩
    | ⟨some e,x⟩ => ⟨.inl e,x⟩
  invFun
    | ⟨.inl e,x⟩ => ⟨some e,x⟩
    | ⟨.inr e,x⟩ => ⟨none,⟨e,x⟩⟩
  left_inv x := by obtain ⟨e,x⟩ := x; cases e <;> rfl
  right_inv x := by obtain ⟨e,x⟩ := x; cases e <;> rfl

noncomputable def frameEdges : Bijection
    ((frame C f cert avoid).expand (grouped C f cert avoid F)).Edge (C.expand F).Edge :=
  (frameEdgeSplit C f cert avoid F).trans
    (Bijection.sigmaMap (frameEdgePartition C f cert avoid) (fun _ => Bijection.refl _))

theorem frame_host (v : (frame C f cert avoid).Vertex) :
    Port.map (frameVertices C f cert avoid F).toFun
      (Net.Expansion.host (frame C f cert avoid) (grouped C f cert avoid F) v) =
    Net.Expansion.host C F (CompleteMatchCut.embed (skeletonOccurrence C f cert avoid).matchEmbedding v) := by
  cases v <;> rfl

theorem frame_local_host (v : A.Vertex) :
    Port.map (frameVertices C f cert avoid F).toFun
      (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) none
        (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
          (Net.Expansion.host (skeleton C f cert avoid) (localFamily C f cert avoid F) v))) =
    Net.Expansion.host C F ((skeletonOccurrence C f cert avoid).ports v) := by
  cases v with
  | internal v =>
    exact congrArg (Net.Expansion.host C F)
      ((skeletonOccurrence C f cert avoid).matchEmbedding.ports_internal v).symm
  | input i =>
    change Port.map _ (Net.Expansion.host _ _ ((frame C f cert avoid).sourcePort none _)) = _
    rw [frame_host]
    exact congrArg (Net.Expansion.host C F)
      ((congrArg (CompleteMatchCut.embed _) (CompleteMatchCut.hole_sourcePort _ _ i)).trans
        (CompleteMatchCut.embed_input _ i))
  | output i =>
    change Port.map _ (Net.Expansion.host _ _ ((frame C f cert avoid).targetPort none _)) = _
    rw [frame_host]
    exact congrArg (Net.Expansion.host C F)
      ((congrArg (CompleteMatchCut.embed _) (CompleteMatchCut.hole_targetPort _ _ i)).trans
        (CompleteMatchCut.embed_output _ i))

theorem frame_sourcePort (e : CompleteMatchCut.RetainedEdge (skeletonOccurrence C f cert avoid).matchEmbedding) (i) :
    CompleteMatchCut.embed (skeletonOccurrence C f cert avoid).matchEmbedding
      ((frame C f cert avoid).sourcePort (some e) i) = C.sourcePort e.val i := by
  simp [Net.sourcePort,frame,CompleteMatchCut.net,CompleteMatchCut.source,
    CompleteMatchCut.retainedSource,CompleteMatchCut.embed_project]

theorem frame_targetPort (e : CompleteMatchCut.RetainedEdge (skeletonOccurrence C f cert avoid).matchEmbedding) (i) :
    CompleteMatchCut.embed (skeletonOccurrence C f cert avoid).matchEmbedding
      ((frame C f cert avoid).targetPort (some e) i) = C.targetPort e.val i := by
  simp [Net.targetPort,frame,CompleteMatchCut.net,CompleteMatchCut.target,
    CompleteMatchCut.retainedTarget,CompleteMatchCut.embed_project]

theorem frame_other (e : CompleteMatchCut.RetainedEdge (skeletonOccurrence C f cert avoid).matchEmbedding)
    (v : (F e.val).Vertex) :
    Port.map (frameVertices C f cert avoid F).toFun
      (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) (some e) v) =
    Net.Expansion.insert C F e.val v := by
  cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Net.Expansion.host _ _ _) = _
    rw [frame_host,frame_sourcePort]; rfl
  | output i =>
    change Port.map _ (Net.Expansion.host _ _ _) = _
    rw [frame_host,frame_targetPort]; rfl

theorem skeleton_sourcePort (e : A.Edge) (i) :
    (skeletonOccurrence C f cert avoid).ports ((skeleton C f cert avoid).sourcePort e i) =
      C.sourcePort (f.edges e).1 i := by
  have h := congrArg (fun xs => xs[i.val]?) ((skeletonOccurrence C f cert avoid).source e)
  change (((skeleton C f cert avoid).source e).map (skeletonOccurrence C f cert avoid).ports)[i.val]? =
    (C.source (f.edges e).1)[i.val]? at h
  have bound : i.val < (C.source (f.edges e).1).length := by rw [C.source_length]; exact i.isLt
  simpa [List.getElem?_eq_getElem,List.getElem_map,Net.sourcePort,
    (skeleton C f cert avoid).source_length,bound,i.isLt] using h

theorem skeleton_targetPort (e : A.Edge) (i) :
    (skeletonOccurrence C f cert avoid).ports ((skeleton C f cert avoid).targetPort e i) =
      C.targetPort (f.edges e).1 i := by
  have h := congrArg (fun xs => xs[i.val]?) ((skeletonOccurrence C f cert avoid).target e)
  change (((skeleton C f cert avoid).target e).map (skeletonOccurrence C f cert avoid).ports)[i.val]? =
    (C.target (f.edges e).1)[i.val]? at h
  have bound : i.val < (C.target (f.edges e).1).length := by rw [C.target_length]; exact i.isLt
  simpa [List.getElem?_eq_getElem,List.getElem_map,Net.targetPort,
    (skeleton C f cert avoid).target_length,bound,i.isLt] using h

theorem frame_local_insert (e : A.Edge) (v : (F (f.edges e).1).Vertex) :
    Port.map (frameVertices C f cert avoid F).toFun
      (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) none
        (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
          (Net.Expansion.insert (skeleton C f cert avoid) (localFamily C f cert avoid F) e v))) =
    Net.Expansion.insert C F (f.edges e).1 v := by
  cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) none
      (Port.cast _ _ (Net.Expansion.host (skeleton C f cert avoid) (localFamily C f cert avoid F)
        ((skeleton C f cert avoid).sourcePort e i)))) = _
    rw [frame_local_host,skeleton_sourcePort]; rfl
  | output i =>
    change Port.map _ (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) none
      (Port.cast _ _ (Net.Expansion.host (skeleton C f cert avoid) (localFamily C f cert avoid F)
        ((skeleton C f cert avoid).targetPort e i)))) = _
    rw [frame_local_host,skeleton_targetPort]; rfl

/-- A single actual finite cut groups precisely the selected original owners.
Both sides may therefore use this same frame with their own filling family. -/
noncomputable def frameIso : DeepIso
    ((frame C f cert avoid).expand (grouped C f cert avoid F)) (C.expand F) where
  vertices := frameVertices C f cert avoid F
  edges := frameEdges C f cert avoid F
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · cases e with
      | none =>
        rcases v with v | ⟨e,v⟩
        · exact (skeletonOccurrence C f cert avoid).internal_label v
        · rfl
      | some e => rfl
  edge_label x := by
    obtain ⟨e,x⟩ := x
    cases e with
    | none => exact labelEquiv_refl d _
    | some e => exact labelEquiv_refl d _
  source x := by
    obtain ⟨e,x⟩ := x
    cases e with
    | none =>
      obtain ⟨e,x⟩ := x
      change (((((F (f.edges e).1).source x).map _).map _).map _).map _ = _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => frame_local_insert C f cert avoid F e v)
    | some e =>
      change (((F e.val).source x).map _).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => frame_other C f cert avoid F e v)
  target x := by
    obtain ⟨e,x⟩ := x
    cases e with
    | none =>
      obtain ⟨e,x⟩ := x
      change (((((F (f.edges e).1).target x).map _).map _).map _).map _ = _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => frame_local_insert C f cert avoid F e v)
    | some e =>
      change (((F e.val).target x).map _).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => frame_other C f cert avoid F e v)

end Hypernets.Copying.RetainedFootprint
