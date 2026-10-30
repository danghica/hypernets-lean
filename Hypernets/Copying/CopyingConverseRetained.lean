import Hypernets.Copying.CopyingConverseRemote
import Hypernets.Copying.CopyingSelectedRetained
import Hypernets.Copying.CopyingTemplateConverseHead

/-! Retained converse copying matches are synthesized by actual selected-spine
extraction. All retention conditions are derived from the resolved payload's
original owner, with no binding-free restriction or assumed locality law. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteRight
open Graph Opening Search.Expansion Remote

/-- A successful right copying path cannot enter a shallow component and
later resolve outside it. Hence a retained terminal payload retains every
selected prefix edge, even when the original supplied tree has other branches. -/
theorem trace_prefix_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand R))
    (last : ∀ name, C.edgeLabel (payload.edges normal.head).1 ≠ primitiveLabel d (.hole name))
    {a : (C.expand R).Edge} {n}
    (path : Trace (CopyTrace.Hop (C.expand R)) a (payload.edges normal.head) n)
    (initial : ∀ name, C.edgeLabel a.1 ≠ primitiveLabel d (.hole name)) :
    ∀ {b m}, Trace (CopyTrace.Hop (C.expand R)) a b m →
      ∀ name, C.edgeLabel b.1 ≠ primitiveLabel d (.hole name) := by
  have kind : CopyTrace.PayloadHead normal.primitive := by
    obtain ⟨e,p,head,kind⟩ := normal.copyable.head_exists
    exact (MatchEmbedding.head_unique normal.head_at head).2 ▸ kind
  have terminal := CopyTrace.head_terminal
    (payload.matchEmbedding.primitive _ _ normal.head_at.1) kind
  generalize destination : payload.edges normal.head = finish at path
  induction path with
  | refl =>
    intro b m route
    cases route with
    | refl => exact initial
    | step hop tail => exact False.elim (terminal _ (destination ▸ hop))
  | @step a b c n hop tail ih =>
    obtain ⟨_,copy⟩ := (cert a.1).retained_of_not_hole initial
    have next (name) : C.edgeLabel b.1 ≠ primitiveLabel d (.hole name) := by
      intro hole
      obtain ⟨w,target,source⟩ := hop.2
      obtain ⟨v,eq⟩ := copy.target_origin target
      obtain ⟨i,input,attached⟩ := source_input_exact C (eq ▸ source)
      obtain ⟨k',h',W,copyable,free,related,owners⟩ :=
        payload_owner C cert closed hole i input normal payload (destination ▸ tail)
      exact last name ((congrArg C.edgeLabel (owners normal.head)).trans hole)
    intro e m route
    cases route with
    | refl => exact initial
    | step first rest =>
      have same := CopyTrace.hop_functional hop first
      subst same
      exact ih next destination rest

/-- A retained payload head retains its whole original copyable payload.
For lambda payloads the box input is a thunk wire, whereas every original
copying hole input is a term wire, so the box cannot be shallowly hidden. -/
theorem payload_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand R))
    (head : ∀ name, C.edgeLabel (payload.edges normal.head).1 ≠ primitiveLabel d (.hole name)) :
    ∀ e name, C.edgeLabel (payload.edges e).1 ≠ primitiveLabel d (.hole name) := by
  intro e name
  rcases normal.edge_cases e with rfl | rfl
  · exact head name
  · cases normal with
    | plain d c => exact head name
    | lambda B =>
      obtain ⟨_,copy⟩ := (cert _).retained_of_not_hole head
      have target := payload.matchEmbedding.target_mem
        (show .internal (CopyRule.NormalForm.lambdaWire B) ∈
          (lambdaPayload B).target (CopyRule.NormalForm.lambda B).head from List.mem_cons_self)
      obtain ⟨v,eq⟩ := copy.target_origin target
      have source := payload.matchEmbedding.source_mem
        (show .internal (CopyRule.NormalForm.lambdaWire B) ∈
          (lambdaPayload B).source (CopyRule.NormalForm.lambda B).tail from List.mem_cons_self)
      apply ConverseOverlap.nonterm_source_not_hole C cert (eq ▸ source) _ _ name
      · have typed : (C.expand R).vertexLabel (Net.Expansion.host C R v) = .thunk 1 := by
          rw [eq]
          exact payload.matchEmbedding.vertexLabel payload.label (.internal (CopyRule.NormalForm.lambdaWire B))
        rw [typed]
        exact Wire.noConfusion
      · intro hole label
        have bad := closed (payload.edges (CopyRule.NormalForm.lambda B).tail)
        rw [label] at bad
        exact bad hole rfl

/-- The actual retained-payload converse case admits a complete selected-spine
copying occurrence. Neither unrelated tree siblings nor arbitrary deep box
bodies are removed from the surrounding original graph. -/
theorem retained_occurrence {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {m k h}
    (T : ContractionTree .term (m+1)) {H : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm H)
    (f : Occurrence (CopyRule.before T H) (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v)
    (last : ∀ name, C.edgeLabel (f.edges (Serial.rightEdge (CopyRule.tree T d) H normal.head)).1 ≠ primitiveLabel d (.hole name)) :
    ∃ n, ∃ U : ContractionTree .term (n+1),
      ∃ g : Occurrence (CopyRule.before U H) (C.expand R),
      g.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v ∧
      RetainedFootprint.AvoidsShallow C g.matchEmbedding := by
  let payload := (Occurrence.serialRight (CopyRule.tree T d) H).comp f
  obtain ⟨cost,a,source,path,label,kind⟩ :=
    (CopyRule.localSuccessorMatch T normal).map f |>.resolves
  have head := (CopyRule.localSuccessorMatch T normal).map f |>.head_at
  have same := (C.expand R).source_unique source head.2
  subst a
  have atHost : MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v)
      ((CopyRule.localSuccessorMatch T normal).map f).active (.contraction .term) :=
    ⟨head.1,attached ▸ head.2⟩
  obtain ⟨⟨retained⟩,originalHead⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away atHost
  have initial (name) : C.edgeLabel ((CopyRule.localSuccessorMatch T normal).map f).active.1 ≠ primitiveLabel d (.hole name) := by
    intro bad
    have impossible := primitiveLabel_injective d (originalHead.1.symm.trans bad)
    cases impossible
  obtain ⟨n,U,g,token,avoid⟩ := selected_occurrence C T H f (by
    intro a entry e n route name
    have input : f.ports (.input ⟨0,by simp⟩) ∈
        (C.expand R).source (f.edges (Serial.leftEdge (CopyRule.tree T d) H a)) := by
      have src := (MatchEmbedding.serialLeft (CopyRule.tree T d) H).source_mem entry
      have moved := f.matchEmbedding.source_mem src
      simpa only [MatchEmbedding.serialLeft,Occurrence.matchEmbedding,Combined.left_input] using moved
    have start := (C.expand R).source_unique input head.2
    have mapped := (route.map (Serial.leftEdge (CopyRule.tree T d) H) (CopyRule.before_tree_hop T H)).map
      f.edges (CopyTrace.hop_map f.matchEmbedding)
    rw [start] at mapped
    exact trace_prefix_avoids C cert closed normal payload last path initial mapped name)
    (payload_avoids C cert closed normal payload last)
  exact ⟨n,U,g,token.trans attached,avoid⟩

end Hypernets.Copying.CopyingTemplate.RemoteRight
