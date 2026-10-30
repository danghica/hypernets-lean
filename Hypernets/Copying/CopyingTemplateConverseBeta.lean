import Hypernets.Copying.CopyingTemplateConverseHead

/-! Complete converse beta footprints remain in the original context. The
lambda body may contain arbitrary deep copying occurrences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ConverseOverlap
open Graph Search.Expansion Opening

/-- Every outer edge of an actual beta footprint avoids a shallow copying
hole. The original left search history proves readiness of both app arguments;
the proof then follows the
lambda's actual boxed successor; it does not inspect the arbitrary box body. -/
theorem beta_avoids {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {v : C.Vertex} (away : ¬ Entering C (.rewrite,v)) {input}
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v)) {k h J}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] J) (stable : Stable G)
    (f : Occurrence (Application.before B G) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  let m := Application.localMatch B G
  have appHead := f.matchEmbedding.head m.head_at
  change MatchEmbedding.HeadAt (C.expand R) (f.ports (.input 0)) (f.edges m.app) (.operation .app) at appHead
  rw [attached] at appHead
  obtain ⟨⟨appCopy⟩,original⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away appHead
  have appAvoid : ∀ name, C.edgeLabel (f.edges m.app).1 ≠ primitiveLabel (d+1) (.hole name) := by
    intro name eq
    rw [original.1] at eq
    cases eq
  have lamAdj : (Application.before B G).Adjacent m.app m.lam :=
    ⟨.internal m.functionWire,by rw [m.app_target]; exact List.mem_cons_self,
      by rw [m.lambda_source]; exact List.mem_cons_self⟩
  have lamAvoid := adjacent_source_not_hole C cert closed away rooted appHead rfl (f.matchEmbedding.adjacent lamAdj)
  obtain ⟨_,lamCopy⟩ := (cert (f.edges m.lam).1).retained_of_not_hole lamAvoid
  have boxTarget := f.matchEmbedding.target_mem
    (show .internal m.thunkWire ∈ (Application.before B G).target m.lam by
      rw [m.lambda_target]; exact List.mem_cons_self)
  obtain ⟨boxPort,boxEq⟩ := lamCopy.target_origin boxTarget
  have boxSource := f.matchEmbedding.source_mem
    (show .internal m.thunkWire ∈ (Application.before B G).source m.boxEdge by
      rw [m.box_source]; exact List.mem_cons_self)
  have boxLabel := f.label m.boxEdge
  have boxNotPrimitive (p : Primitive) :
      (C.expand R).edgeLabel (f.edges m.boxEdge) ≠ primitiveLabel (d+1) p := by
    intro eq
    rw [eq] at boxLabel
    exact boxLabel
  have boxType : (C.expand R).vertexLabel (Net.Expansion.host C R boxPort) = .thunk 1 := by
    rw [boxEq]
    exact f.matchEmbedding.vertexLabel f.label (.internal m.thunkWire)
  have boxAvoid := nonterm_source_not_hole C cert (boxEq ▸ boxSource)
    (by rw [boxType]; exact Wire.noConfusion) (fun name => boxNotPrimitive (.hole name))
  intro a name
  obtain ⟨part,a⟩ := a
  cases part with
  | false => cases DiscardResult.fin_one a; exact appAvoid name
  | true =>
    obtain ⟨part,a⟩ := a
    cases part with
    | false =>
      obtain ⟨part,a⟩ := a
      cases part <;> cases DiscardResult.fin_one a
      · exact lamAvoid name
      · exact boxAvoid name
    | true =>
      apply adjacent_source_not_hole C cert closed away rooted appHead rfl
      · apply f.matchEmbedding.adjacent
        refine ⟨Application.argument B G 1,?_,?_⟩
        · change Application.argument B G 1 ∈ [_,Application.argument B G 1]
          simp
        · exact List.mem_map_of_mem (List.mem_map_of_mem (Stable.input_source stable.labels a))


end Hypernets.Copying.CopyingTemplate.ConverseOverlap
