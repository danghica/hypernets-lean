import Hypernets.Copying.CopyingTemplateForwardBarrier
import Hypernets.Copying.NullaryDeepOverlap

/-! The actual beta footprint cannot enter a shallow left copying component:
its entire outer application/lambda/box/argument ancestry contains no term
contraction, including when the arbitrary body has deep template holes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ForwardOverlap
open Graph Combined Opening Search.Expansion

/-- Every outer beta edge is reached from the application: the lambda and its
box are a two-edge path, and every stable argument edge uses its sole input. -/
theorem beta_avoids {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {v : C.Vertex} {k h J}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] J) (stable : Stable G)
    (f : Occurrence (Application.before B G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  have different (e : (Application.before B G).Edge) :
      (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel (d+1) (.contraction .term) := by
    intro label
    have original := (Search.primitive_equiv (f.label e) (.contraction .term)).mpr label
    obtain ⟨part,e⟩ := e
    cases part with
    | false => cases original
    | true =>
      obtain ⟨part,e⟩ := e
      cases part with
      | false =>
        obtain ⟨part,e⟩ := e
        cases part <;> cases original
      | true =>
        exact OperationalTemplates.stable_primitive stable e (.contraction .term) original
  let m := Application.localMatch B G
  have headSource : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges m.app) := by
    rw [← attached]
    exact f.matchEmbedding.source_mem m.head_at.2
  have avoid (e) (path : Ancestor (Application.before B G) m.app e) :
      ∀ name, C.edgeLabel (f.edges e).1 ≠ primitiveLabel (d+1) (.hole name) :=
    ancestor_not_hole C cert f.matchEmbedding different closed headSource path
  have lamAdj : (Application.before B G).Adjacent m.app m.lam :=
    ⟨.internal m.functionWire,by rw [m.app_target]; exact List.mem_cons_self,
      by rw [m.lambda_source]; exact List.mem_cons_self⟩
  have boxAdj : (Application.before B G).Adjacent m.lam m.boxEdge :=
    ⟨.internal m.thunkWire,by rw [m.lambda_target]; exact List.mem_cons_self,
      by rw [m.box_source]; exact List.mem_cons_self⟩
  intro e name
  obtain ⟨part,e⟩ := e
  cases part with
  | false => cases DiscardResult.fin_one e; exact avoid m.app (.refl _) name
  | true =>
    obtain ⟨part,e⟩ := e
    cases part with
    | false =>
      obtain ⟨part,e⟩ := e
      cases part <;> cases DiscardResult.fin_one e
      · exact avoid m.lam (.step lamAdj (.refl _)) name
      · exact avoid m.boxEdge (.step lamAdj (.step boxAdj (.refl _))) name
    | true =>
      apply avoid _ _ name
      apply Ancestor.step _ (.refl _)
      refine ⟨Application.argument B G 1,?_,?_⟩
      · change Application.argument B G 1 ∈ [_,Application.argument B G 1]
        simp
      · exact List.mem_map_of_mem (List.mem_map_of_mem (Stable.input_source stable.labels e))

end Hypernets.Copying.CopyingTemplate.ForwardOverlap
