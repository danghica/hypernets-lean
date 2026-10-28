import Hypernets.Copying.MinimalCopyOccurrence
import Hypernets.Copying.ConverseClassification

/-! Rematching selects precisely the copied contraction spine. Binding freedom
excludes shallow holes along that spine and through the entire actual payload;
unused sibling branches need no exclusion hypothesis. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingOverlap
open Graph Opening Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
include cert free away

omit cert free away in
/-- A counted adjacency path also supplies its uncounted ancestry. -/
theorem trace_ancestor {d I O} {G : Hypernet d I O} {a b n}
    (path : Trace G.Adjacent a b n) : Ancestor G a b := by
  induction path with
  | refl => exact .refl _
  | step first rest ih => exact .step first ih

/-- A normalized payload and the actual selected spine form a complete
retained footprint, for any directed template relation. -/
theorem normal_minimal_copy_occurrence {m k h} (tree : ContractionTree .term (m+1))
    {G : Hypernet d [.term] (environmentInterface k h)} (normal : CopyRule.NormalForm G)
    (f : Occurrence (CopyRule.before tree G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    ∃ n orientation,
      ∃ g : Occurrence (CopyRule.before (ContractionSpine.tree .term n orientation) G) (C.expand L),
        g.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v ∧
        RetainedFootprint.AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,g,input,_,a,source,paths⟩ := CopyRule.minimal_occurrence tree G ⟨0,by simp⟩
  let placed := g.comp f
  have token : placed.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v :=
    (congrArg f.ports input).trans attached
  have head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) (f.edges a) (.contraction .term) := by
    obtain ⟨b,label,src⟩ := CopyRule.before_active_head tree G ⟨0,by simp⟩
    have eq := (CopyRule.before tree G).source_unique source src
    subst a
    rw [← attached]
    exact f.matchEmbedding.head ⟨label,src⟩
  have payload (e : G.Edge) (hole : Hole) :
      C.edgeLabel (placed.edges (Serial.rightEdge (CopyRule.tree (ContractionSpine.tree .term n orientation) d) G e)).1 ≠
        primitiveLabel d (.hole hole) := by
    let matched := (CopyRule.localSuccessorMatch (ContractionSpine.tree .term n orientation) normal).map placed
    have aux (w) (eq : w = Net.Expansion.host C L v) (m : CopyRule.SuccessorMatch (C.expand L) w G) :
        C.edgeLabel (m.payload.edges e).1 ≠ primitiveLabel d (.hole hole) := by
      subst w
      exact copying_payload_not_hole C cert free away m e hole
    exact aux _ token matched
  have treeAvoid (e : Fin (n+1)) (hole : Hole) :
      C.edgeLabel
        (placed.edges (Serial.leftEdge (CopyRule.tree (ContractionSpine.tree .term n orientation) d) G e)).1 ≠
        primitiveLabel d (.hole hole) := by
    have path := trace_ancestor ((paths e).map f.edges f.matchEmbedding.adjacent)
    obtain ⟨⟨retained⟩,_⟩ := contraction_descendant C cert free away head path
    have label : (C.expand L).edgeLabel
        (placed.edges (Serial.leftEdge (CopyRule.tree (ContractionSpine.tree .term n orientation) d) G e)) =
        primitiveLabel d (.contraction .term) :=
      placed.matchEmbedding.primitive _ _ (by cases d <;> rfl)
    have original : C.edgeLabel
        (placed.edges (Serial.leftEdge (CopyRule.tree (ContractionSpine.tree .term n orientation) d) G e)).1 =
        primitiveLabel d (.contraction .term) := by
      apply (retained.primitive _).mp
      change (L (f.edges (g.edges (Serial.leftEdge _ _ e))).1).edgeLabel
        (f.edges (g.edges (Serial.leftEdge _ _ e))).2 = _ at label
      simpa only [retained.only] using label
    rw [original]
    intro eq
    cases primitiveLabel_injective d eq
  refine ⟨n,orientation,placed,token,?_⟩
  intro edge hole
  obtain ⟨part,e⟩ := edge
  cases part with
  | false => cases d <;> exact treeAvoid e hole
  | true => cases d <;> exact payload e hole

/-- Original payload normalization is only a representation isomorphism.
Every actual copying occurrence therefore supplies a complete retained local
copying occurrence with an unchanged original machine rule. -/
theorem minimal_copy_occurrence {m k h} (tree : ContractionTree .term (m+1))
    {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G)
    (f : Occurrence (CopyRule.before tree G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    ∃ n orientation, ∃ H : Hypernet d [.term] (environmentInterface k h), Copyable H ∧
      ∃ g : Occurrence (CopyRule.before (ContractionSpine.tree .term n orientation) H) (C.expand L),
        g.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v ∧
        RetainedFootprint.AvoidsShallow C g.matchEmbedding := by
  obtain ⟨H,⟨normal⟩,⟨iso⟩⟩ := CopyRule.normal_form copyable
  let whole := CopyRule.before_congr (Net.Iso.refl tree.net) iso
  let normalized := (Occurrence.ofIso whole.symm).comp f
  obtain ⟨n,orientation,g,token,avoid⟩ := normal_minimal_copy_occurrence C cert free away tree normal normalized attached
  exact ⟨n,orientation,H,normal.copyable,g,token,avoid⟩
end Hypernets.Copying.BindingOverlap
