import Hypernets.Copying.CompleteMatchRewrite

/-! An edge-disjoint complete occurrence survives actual replacement of another
complete occurrence. Completeness proves the necessary vertex freshness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O J K L M} {A : Hypernet d J K} {B : Hypernet d L M}
    {G : Hypernet d I O} (f : Occurrence A G) (g : Occurrence B G)
    (disjoint : ∀ a b, f.edges a ≠ g.edges b)

/-- Each edge of the other occurrence belongs to the computed complement. -/
def cutEdge (e : B.Edge) : CompleteMatchCut.RetainedEdge f.matchEmbedding :=
  ⟨g.edges e,fun a => disjoint a e⟩

include disjoint in
/-- Every port of a disjoint complete occurrence lies outside the removed
internal vertices, even when the two occurrences share boundary wires. -/
theorem outsideCut (v : B.Vertex) : CompleteMatchCut.Outside f.matchEmbedding (g.ports v) := by
  by_cases output : v.IsOutput
  · obtain ⟨e,mem⟩ := (B.target_coverage v).mpr (by
      cases v <;> simp_all [Port.IsOutput,Port.IsInput])
    exact CompleteMatchCut.outside_target f.matchEmbedding (cutEdge f g disjoint e)
      (g.matchEmbedding.target_mem mem)
  · obtain ⟨e,mem⟩ := (B.source_coverage v).mpr output
    exact CompleteMatchCut.outside_source f.matchEmbedding (cutEdge f g disjoint e)
      (g.matchEmbedding.source_mem mem)

/-- Project the surviving occurrence into the complement's retained vertices. -/
def cutPort (v : B.Vertex) : CompleteMatchCut.Vertex f.matchEmbedding :=
  CompleteMatchCut.project f.matchEmbedding (g.ports v) (outsideCut f g disjoint v)

include disjoint in
theorem cutPort_internal (v : B.Internal) : cutPort f g disjoint (.internal v) =
    .internal ⟨g.internals v,by
      have h := outsideCut f g disjoint (.internal v)
      rw [g.internal_map] at h
      exact h⟩ := by
  apply CompleteMatchCut.embed_injective f.matchEmbedding
  change CompleteMatchCut.embed f.matchEmbedding
    (CompleteMatchCut.project f.matchEmbedding (g.ports (.internal v)) _) = _
  rw [CompleteMatchCut.embed_project]
  exact g.internal_map v

include disjoint in
theorem cutPort_source (e : B.Edge) :
    (B.source e).map (cutPort f g disjoint) =
      CompleteMatchCut.retainedSource f.matchEmbedding (cutEdge f g disjoint e) := by
  apply (List.map_inj_right (f := CompleteMatchCut.embed f.matchEmbedding)
    (fun _ _ h => CompleteMatchCut.embed_injective f.matchEmbedding h)).mp
  rw [CompleteMatchCut.embed_retainedSource]
  simp only [List.map_map,Function.comp_def,cutPort,CompleteMatchCut.embed_project]
  exact g.source e

include disjoint in
theorem cutPort_target (e : B.Edge) :
    (B.target e).map (cutPort f g disjoint) =
      CompleteMatchCut.retainedTarget f.matchEmbedding (cutEdge f g disjoint e) := by
  apply (List.map_inj_right (f := CompleteMatchCut.embed f.matchEmbedding)
    (fun _ _ h => CompleteMatchCut.embed_injective f.matchEmbedding h)).mp
  rw [CompleteMatchCut.embed_retainedTarget]
  simp only [List.map_map,Function.comp_def,cutPort,CompleteMatchCut.embed_project]
  exact g.target e

/-- The surviving occurrence, with all unmatched incidences carried through
the actual computed replacement. -/
noncomputable def acrossCut (N : Hypernet d J K) :
    Occurrence B (CompleteMatchCut.replaceWith f.matchEmbedding f.label N) where
  ports v := Net.Replacement.host (CompleteMatchCut.net f.matchEmbedding f.label) none
    (N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
      (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm) (cutPort f g disjoint v)
  internals v := .inl ⟨g.internals v,by
    have h := outsideCut f g disjoint (.internal v)
    rw [g.internal_map] at h
    exact h⟩
  edges e := .inl ⟨some (cutEdge f g disjoint e),Option.some_ne_none _⟩
  internal_map v := by rw [cutPort_internal]; rfl
  internal_injective := by
    intro a b eq
    exact g.internal_injective (congrArg Subtype.val (Sum.inl.inj eq))
  edge_injective := by
    intro a b eq
    exact g.edge_injective (congrArg Subtype.val (Option.some.inj
      (congrArg Subtype.val (Sum.inl.inj eq))))
  internal_label v := g.internal_label v
  label e := g.label e
  source e := by
    have eq := congrArg (List.map (Net.Replacement.host
      (CompleteMatchCut.net f.matchEmbedding f.label) none
      (N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
        (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm)))
      (cutPort_source f g disjoint e)
    simpa only [CompleteMatchCut.replaceWith,Net.plug,Net.Replacement.source,
      Net.Replacement.target,CompleteMatchCut.net,CompleteMatchCut.source,CompleteMatchCut.target,
      List.map_map,Function.comp_def] using eq
  target e := by
    have eq := congrArg (List.map (Net.Replacement.host
      (CompleteMatchCut.net f.matchEmbedding f.label) none
      (N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
        (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm)))
      (cutPort_target f g disjoint e)
    simpa only [CompleteMatchCut.replaceWith,Net.plug,Net.Replacement.source,
      Net.Replacement.target,CompleteMatchCut.net,CompleteMatchCut.source,CompleteMatchCut.target,
      List.map_map,Function.comp_def] using eq

end Hypernets.Copying.Opening.Occurrence
