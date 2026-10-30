import Hypernets.Copying.CopyingTemplateRemoteRetained
import Hypernets.Copying.MinimalCopyOccurrence

/-! Retain exactly the selected spine of an original copying match. The
complete payload remains unchanged, while unrelated tree branches become
ordered side inputs of the smaller actual source occurrence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.Remote
open Graph Opening Search.Expansion

/-- Given proved retention along the actual selected input's paths and on
the full payload, minimal-spine extraction supplies a complete retained
original copying source. No assumption is made about unrelated siblings. -/
theorem selected_occurrence {d I O} (C : Hypernet d I O) {F}
    {m k h} (T : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (f : Occurrence (CopyRule.before T H) (C.expand F))
    (paths : ∀ a, Port.input ⟨0,by simp⟩ ∈ T.net.source a →
      ∀ e n, Trace T.net.Adjacent a e n → ∀ name,
        C.edgeLabel (f.edges (Serial.leftEdge (CopyRule.tree T d) H e)).1 ≠ primitiveLabel d (.hole name))
    (payload : ∀ e name, C.edgeLabel (f.edges (Serial.rightEdge (CopyRule.tree T d) H e)).1 ≠ primitiveLabel d (.hole name)) :
    ∃ n, ∃ U : ContractionTree .term (n+1),
      ∃ g : Occurrence (CopyRule.before U H) (C.expand F),
      g.ports (.input ⟨0,by simp⟩) = f.ports (.input ⟨0,by simp⟩) ∧
      RetainedFootprint.AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,g,first,last,a,entry,pre⟩ := T.minimal_spine d ⟨0,by simp⟩
  have outputs : ∀ j, g.ports (.output j) = .output j := by
    intro j
    have zero : j = 0 := Fin.ext (by have := j.isLt; simp_all)
    subst j
    exact last
  let inside :=  Occurrence.SerialExtension.occurrence g H outputs
  refine ⟨n+1,ContractionSpine.tree .term n orientation,inside.comp f,?_,?_⟩
  · change f.ports (inside.ports (.input ⟨0,by simp⟩)) = _
    rw [Occurrence.SerialExtension.occurrence_input g H outputs _ _ first]
  · cases d
    all_goals
      rintro ⟨side,e⟩ name hole
      cases side
      · exact paths a entry _ e.val (pre e) name hole
      · exact payload e name hole

/-- In the retained-payload case, every selected source contraction and every
payload edge are proved to avoid shallow copying holes. The resulting smaller
source is an actual full-label occurrence at exactly the original token. -/
theorem retained_occurrence {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {m k h}
    (T : ContractionTree .term (m+1)) {H : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm H)
    (f : Occurrence (CopyRule.before T H) (C.expand L))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (last : ∀ name, C.edgeLabel (f.edges (Serial.rightEdge (CopyRule.tree T d) H normal.head)).1 ≠ primitiveLabel d (.hole name)) :
    ∃ n, ∃ U : ContractionTree .term (n+1),
      ∃ g : Occurrence (CopyRule.before U H) (C.expand L),
      g.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v ∧
      RetainedFootprint.AvoidsShallow C g.matchEmbedding := by
  let payload := (Occurrence.serialRight (CopyRule.tree T d) H).comp f
  obtain ⟨cost,a,source,path,label,kind⟩ :=
    (CopyRule.localSuccessorMatch T normal).map f |>.resolves
  have head := (CopyRule.localSuccessorMatch T normal).map f |>.head_at
  have same := (C.expand L).source_unique source head.2
  subst a
  have atHost : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v)
      ((CopyRule.localSuccessorMatch T normal).map f).active (.contraction .term) :=
    ⟨head.1,attached ▸ head.2⟩
  obtain ⟨⟨retained⟩,originalHead⟩ := BindingOverlap.head_retained C cert away atHost
  have initial (name) : C.edgeLabel ((CopyRule.localSuccessorMatch T normal).map f).active.1 ≠ primitiveLabel d (.hole name) := by
    intro bad
    have impossible := primitiveLabel_injective d (originalHead.1.symm.trans bad)
    cases impossible
  obtain ⟨n,U,g,token,avoid⟩ := selected_occurrence C T H f (by
    intro a entry e n route name
    have input : f.ports (.input ⟨0,by simp⟩) ∈
        (C.expand L).source (f.edges (Serial.leftEdge (CopyRule.tree T d) H a)) := by
      have src := (MatchEmbedding.serialLeft (CopyRule.tree T d) H).source_mem entry
      have moved := f.matchEmbedding.source_mem src
      simpa only [MatchEmbedding.serialLeft,Occurrence.matchEmbedding,Combined.left_input] using moved
    have start := (C.expand L).source_unique input head.2
    have mapped := (route.map (Serial.leftEdge (CopyRule.tree T d) H) (CopyRule.before_tree_hop T H)).map
      f.edges (CopyTrace.hop_map f.matchEmbedding)
    rw [start] at mapped
    exact trace_prefix_avoids C cert closed normal payload last path initial mapped name)
    (payload_avoids C cert closed normal payload last)
  exact ⟨n,U,g,token.trans attached,avoid⟩

end Hypernets.Copying.CopyingTemplate.Remote
