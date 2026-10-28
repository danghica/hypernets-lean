import Hypernets.Copying.NullaryFootprint
import Hypernets.Copying.NullaryBindingFree
import Hypernets.Copying.ConverseCopyFootprint

/-! Actual beta and copying footprints for nullary templates. Every required
restriction follows from the original recursive filling and its closed endpoint. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.NullaryOverlap
open Graph Combined Opening Search.Expansion

/-- Every outer beta edge is reached from the application: the lambda and its
box are a two-edge path, and every stable argument edge uses its sole input. -/
theorem beta_avoids {T : PreTemplate} {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
    (closed : HoleFree (C.expand L)) {v : C.Vertex} {k h J}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] J) (stable : Stable G)
    (f : Occurrence (Application.before B G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  let m := Application.localMatch B G
  have headSource : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges m.app) := by
    rw [← attached]
    exact f.matchEmbedding.source_mem m.head_at.2
  have avoid (e) (path : Ancestor (Application.before B G) m.app e) :
      ∀ name, C.edgeLabel (f.edges e).1 ≠ primitiveLabel (d+1) (.hole name) :=
    ancestor_not_hole C cert none closed headSource (path.map f.edges f.matchEmbedding.adjacent)
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

/-- The complete actual copying payload and selected contraction spine are
retained. Any irrelevant branches of the supplied tree remain in the complement. -/
theorem minimal_copy_occurrence {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
    (free : FocusFree C) (closed : HoleFree (C.expand L)) {v : C.Vertex}
    {m k h} (tree : ContractionTree .term (m+1))
    {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G)
    (f : Occurrence (CopyRule.before tree G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    ∃ n orientation, ∃ H : Hypernet d [.term] (environmentInterface k h), Copyable H ∧
      ∃ g : Occurrence (CopyRule.before (ContractionSpine.tree .term n orientation) H) (C.expand L),
        g.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v ∧
        RetainedFootprint.AvoidsShallow C g.matchEmbedding :=
  BindingOverlap.minimal_copy_occurrence C cert
    ((DeepFilling.expand C L R cert).nullary_bindingFree none free closed)
    (not_entering C cert none closed (.rewrite,v)) tree copyable f attached
end Hypernets.Copying.NullaryOverlap
