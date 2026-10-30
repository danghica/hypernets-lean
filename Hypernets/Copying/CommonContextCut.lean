import Hypernets.Copying.RetainedFootprintFrame

/-! A complete finite cut in the original common context may contain original
shallow template holes. Both whole expansions factor through that same cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph
variable {d I O} (C : Hypernet d I O) {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A C)

/-- Normalize only local label representation to the actual original host;
carriers, ordered incidences and every attachment coordinate stay unchanged. -/
noncomputable def skeleton : Hypernet d J K :=
  A.relabelEdges (alphabet d).signature (fun e => C.edgeLabel ((f.edges e)))
    (fun e => (labelEquiv_input d (f.label e)).symm)
    (fun e => (labelEquiv_output d (f.label e)).symm)

/-- The normalized common fragment has a complete literal-label occurrence. -/
noncomputable def skeletonOccurrence : Opening.Occurrence (skeleton C f) C :=
  (show MatchEmbedding (skeleton C f) C from {
    ports := f.ports
    edges := f.edges
    edge_injective := f.edge_injective
    primitive _ _ eq := eq
    source := f.source
    target := f.target
  }).occurrence (fun _ => labelEquiv_refl _ _)

noncomputable def frame : Hypernet d I O :=
  CompleteMatchCut.net (skeletonOccurrence C f).matchEmbedding
    (skeletonOccurrence C f).label

variable (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
  ((alphabet d).signature.output (C.edgeLabel e)))

noncomputable def localFamily (e : (skeleton C f).Edge) := F (f.edges e)

noncomputable def grouped (e : (frame C f).Edge) : Hypernet d
    ((alphabet d).signature.input ((frame C f).edgeLabel e))
    ((alphabet d).signature.output ((frame C f).edgeLabel e)) :=
  match e with
  | none => ((skeleton C f).expand (localFamily C f F)).reboundary
      (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
  | some e => F e.val

noncomputable def frameEdgePartition : Bijection
    (CompleteMatchCut.RetainedEdge (skeletonOccurrence C f).matchEmbedding ⊕ A.Edge) C.Edge :=
  Bijection.ofComplement (fun e => (f.edges e)) (f.edge_injective)

/-- Regroup only the carrier tags; no vertex is created or discarded. -/
noncomputable def frameVertexSplit : Bijection
    ((frame C f).expand (grouped C f F)).Internal
    ((CompleteMatchCut.Internal (skeletonOccurrence C f).matchEmbedding ⊕ A.Internal) ⊕
      (Σ e, (F ((frameEdgePartition C f).toFun e)).Internal)) where
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
    ((frame C f).expand (grouped C f F)).Internal (C.expand F).Internal :=
  (frameVertexSplit C f F).trans
    ((CompleteMatchCut.vertices (skeletonOccurrence C f).matchEmbedding).sum
      (Bijection.sigmaMap (frameEdgePartition C f) (fun _ => Bijection.refl _)))

noncomputable def frameEdgeSplit : Bijection
    ((frame C f).expand (grouped C f F)).Edge
    (Σ e, (F ((frameEdgePartition C f).toFun e)).Edge) where
  toFun
    | ⟨none,⟨e,x⟩⟩ => ⟨.inr e,x⟩
    | ⟨some e,x⟩ => ⟨.inl e,x⟩
  invFun
    | ⟨.inl e,x⟩ => ⟨some e,x⟩
    | ⟨.inr e,x⟩ => ⟨none,⟨e,x⟩⟩
  left_inv x := by obtain ⟨e,x⟩ := x; cases e <;> rfl
  right_inv x := by obtain ⟨e,x⟩ := x; cases e <;> rfl

noncomputable def frameEdges : Bijection
    ((frame C f).expand (grouped C f F)).Edge (C.expand F).Edge :=
  (frameEdgeSplit C f F).trans
    (Bijection.sigmaMap (frameEdgePartition C f) (fun _ => Bijection.refl _))

theorem frame_host (v : (frame C f).Vertex) :
    Port.map (frameVertices C f F).toFun
      (Net.Expansion.host (frame C f) (grouped C f F) v) =
    Net.Expansion.host C F (CompleteMatchCut.embed (skeletonOccurrence C f).matchEmbedding v) := by
  cases v <;> rfl

theorem frame_local_host (v : A.Vertex) :
    Port.map (frameVertices C f F).toFun
      (Net.Expansion.insert (frame C f) (grouped C f F) none
        (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
          (Net.Expansion.host (skeleton C f) (localFamily C f F) v))) =
    Net.Expansion.host C F ((skeletonOccurrence C f).ports v) := by
  cases v with
  | internal v =>
    exact congrArg (Net.Expansion.host C F)
      ((skeletonOccurrence C f).matchEmbedding.ports_internal v).symm
  | input i =>
    change Port.map _ (Net.Expansion.host _ _ ((frame C f).sourcePort none _)) = _
    rw [frame_host]
    exact congrArg (Net.Expansion.host C F)
      ((congrArg (CompleteMatchCut.embed _) (CompleteMatchCut.hole_sourcePort _ _ i)).trans
        (CompleteMatchCut.embed_input _ i))
  | output i =>
    change Port.map _ (Net.Expansion.host _ _ ((frame C f).targetPort none _)) = _
    rw [frame_host]
    exact congrArg (Net.Expansion.host C F)
      ((congrArg (CompleteMatchCut.embed _) (CompleteMatchCut.hole_targetPort _ _ i)).trans
        (CompleteMatchCut.embed_output _ i))

theorem frame_sourcePort (e : CompleteMatchCut.RetainedEdge (skeletonOccurrence C f).matchEmbedding) (i) :
    CompleteMatchCut.embed (skeletonOccurrence C f).matchEmbedding
      ((frame C f).sourcePort (some e) i) = C.sourcePort e.val i := by
  simp [Net.sourcePort,frame,CompleteMatchCut.net,CompleteMatchCut.source,
    CompleteMatchCut.retainedSource,CompleteMatchCut.embed_project]

theorem frame_targetPort (e : CompleteMatchCut.RetainedEdge (skeletonOccurrence C f).matchEmbedding) (i) :
    CompleteMatchCut.embed (skeletonOccurrence C f).matchEmbedding
      ((frame C f).targetPort (some e) i) = C.targetPort e.val i := by
  simp [Net.targetPort,frame,CompleteMatchCut.net,CompleteMatchCut.target,
    CompleteMatchCut.retainedTarget,CompleteMatchCut.embed_project]

theorem frame_other (e : CompleteMatchCut.RetainedEdge (skeletonOccurrence C f).matchEmbedding)
    (v : (F e.val).Vertex) :
    Port.map (frameVertices C f F).toFun
      (Net.Expansion.insert (frame C f) (grouped C f F) (some e) v) =
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
    (skeletonOccurrence C f).ports ((skeleton C f).sourcePort e i) =
      C.sourcePort (f.edges e) i := by
  have h := congrArg (fun xs => xs[i.val]?) ((skeletonOccurrence C f).source e)
  change (((skeleton C f).source e).map (skeletonOccurrence C f).ports)[i.val]? =
    (C.source (f.edges e))[i.val]? at h
  have bound : i.val < (C.source (f.edges e)).length := by rw [C.source_length]; exact i.isLt
  simpa [List.getElem?_eq_getElem,List.getElem_map,Net.sourcePort,
    (skeleton C f).source_length,bound,i.isLt] using h

theorem skeleton_targetPort (e : A.Edge) (i) :
    (skeletonOccurrence C f).ports ((skeleton C f).targetPort e i) =
      C.targetPort (f.edges e) i := by
  have h := congrArg (fun xs => xs[i.val]?) ((skeletonOccurrence C f).target e)
  change (((skeleton C f).target e).map (skeletonOccurrence C f).ports)[i.val]? =
    (C.target (f.edges e))[i.val]? at h
  have bound : i.val < (C.target (f.edges e)).length := by rw [C.target_length]; exact i.isLt
  simpa [List.getElem?_eq_getElem,List.getElem_map,Net.targetPort,
    (skeleton C f).target_length,bound,i.isLt] using h

theorem frame_local_insert (e : A.Edge) (v : (F (f.edges e)).Vertex) :
    Port.map (frameVertices C f F).toFun
      (Net.Expansion.insert (frame C f) (grouped C f F) none
        (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
          (Net.Expansion.insert (skeleton C f) (localFamily C f F) e v))) =
    Net.Expansion.insert C F (f.edges e) v := by
  cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Net.Expansion.insert (frame C f) (grouped C f F) none
      (Port.cast _ _ (Net.Expansion.host (skeleton C f) (localFamily C f F)
        ((skeleton C f).sourcePort e i)))) = _
    rw [frame_local_host,skeleton_sourcePort]; rfl
  | output i =>
    change Port.map _ (Net.Expansion.insert (frame C f) (grouped C f F) none
      (Port.cast _ _ (Net.Expansion.host (skeleton C f) (localFamily C f F)
        ((skeleton C f).targetPort e i)))) = _
    rw [frame_local_host,skeleton_targetPort]; rfl

/-- A single actual finite cut groups precisely the selected original owners.
Both sides may therefore use this same frame with their own filling family. -/
noncomputable def frameIso : DeepIso
    ((frame C f).expand (grouped C f F)) (C.expand F) where
  vertices := frameVertices C f F
  edges := frameEdges C f F
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · cases e with
      | none =>
        rcases v with v | ⟨e,v⟩
        · exact (skeletonOccurrence C f).internal_label v
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
      change (((((F (f.edges e)).source x).map _).map _).map _).map _ = _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => frame_local_insert C f F e v)
    | some e =>
      change (((F e.val).source x).map _).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => frame_other C f F e v)
  target x := by
    obtain ⟨e,x⟩ := x
    cases e with
    | none =>
      obtain ⟨e,x⟩ := x
      change (((((F (f.edges e)).target x).map _).map _).map _).map _ = _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => frame_local_insert C f F e v)
    | some e =>
      change (((F e.val).target x).map _).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => frame_other C f F e v)

end Hypernets.Copying.CommonContextCut
