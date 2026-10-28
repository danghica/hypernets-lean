import Hypernets.Copying.OperationalStableOverlap

/-! Complete forward beta footprints remain in the original context. The
lambda body may contain arbitrary deep operational occurrences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ForwardOverlap
open Graph Search.Expansion Opening

/-- Every outer edge of an actual beta footprint avoids a shallow operational
hole. The proof follows the app's ordered function/argument edges and the
lambda's actual boxed successor; it does not inspect the arbitrary box body. -/
theorem beta_avoids {kind d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v)) {k h J}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] J) (stable : Stable G)
    (f : Occurrence (Application.before B G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  let m := Application.localMatch B G
  have appHead := f.matchEmbedding.head m.head_at
  change MatchEmbedding.HeadAt (C.expand L) (f.ports (.input 0)) (f.edges m.app) (.operation .app) at appHead
  rw [attached] at appHead
  obtain ⟨⟨appCopy⟩,original⟩ := BindingOverlap.head_retained C cert away appHead
  have appAvoid : ∀ name, C.edgeLabel (f.edges m.app).1 ≠ primitiveLabel (d+1) (.hole name) := by
    intro name eq
    rw [original.1] at eq
    cases eq
  have lamAdj : (Application.before B G).Adjacent m.app m.lam :=
    ⟨.internal m.functionWire,by rw [m.app_target]; exact List.mem_cons_self,
      by rw [m.lambda_source]; exact List.mem_cons_self⟩
  have lamAvoid := stable_after_retained C cert appCopy (f.matchEmbedding.adjacent lamAdj)
    ⟨.operation .lam,f.matchEmbedding.primitive _ _ m.lambda_label,rfl⟩
  obtain ⟨lamCopy,_⟩ := (cert (f.edges m.lam).1).retained_of_not_hole lamAvoid
  have boxTarget := f.matchEmbedding.target_mem
    (show .internal m.thunkWire ∈ (Application.before B G).target m.lam by
      rw [m.lambda_target]; exact List.mem_cons_self)
  obtain ⟨boxPort,boxEq⟩ := lamCopy.target_origin boxTarget
  have boxSource := f.matchEmbedding.source_mem
    (show .internal m.thunkWire ∈ (Application.before B G).source m.boxEdge by
      rw [m.box_source]; exact List.mem_cons_self)
  have boxLabel := f.label m.boxEdge
  have boxNotPrimitive (p : Primitive) :
      (C.expand L).edgeLabel (f.edges m.boxEdge) ≠ primitiveLabel (d+1) p := by
    intro eq
    rw [eq] at boxLabel
    exact boxLabel
  have boxAvoid := source_not_hole C cert (boxEq ▸ boxSource)
    (boxNotPrimitive (.operation kind.head)) (fun name => boxNotPrimitive (.hole name))
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
      apply stable_after_retained C cert appCopy
      · apply f.matchEmbedding.adjacent
        refine ⟨Application.argument B G 1,?_,?_⟩
        · change Application.argument B G 1 ∈ [_,Application.argument B G 1]
          simp
        · exact List.mem_map_of_mem (List.mem_map_of_mem (Stable.input_source stable.labels a))
      · obtain ⟨p,label,passive⟩ := stable.labels a
        exact ⟨p,f.matchEmbedding.primitive _ _ label,passive⟩

end Hypernets.Copying.OperationalTemplates.ForwardOverlap
