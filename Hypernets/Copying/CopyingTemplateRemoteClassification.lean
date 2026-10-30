import Hypernets.Copying.CopyingTemplateFirstShallow
import Hypernets.Copying.CopyingRemoteSpine
import Hypernets.Copying.CopyingTemplateRemotePayload

/-! Complete first-entry classification of an actual remote copying request.
The original term-contraction prefix is realized as a finite source occurrence;
its selected output attaches to the exact original hole input. The matched
payload is forced to be the entered component's complete recursive payload. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.Remote
open Graph Opening Search.Expansion

/-- The actual payload selected by a supplied copy match has every edge in
the entered shallow component, and agrees with its complete recursive payload. -/
theorem payload_owner {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {hole : C.Edge} {name}
    (label : C.edgeLabel hole = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    {entry : (L hole).Edge} (source : Port.input i ∈ (L hole).source entry)
    {k h} {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand L)) {n}
    (suffix : Trace (CopyTrace.Hop (C.expand L)) ⟨hole,entry⟩ (payload.edges normal.head) n) :
    ∃ k' h', ∃ W : Hypernet d [.term] (environmentInterface k' h'),
      Copyable W ∧ FocusFree W ∧ CopyRule.PayloadRelated V W ∧
      (∀ e, (payload.edges e).1 = hole) := by
  have kind : CopyTrace.PayloadHead normal.primitive := by
    obtain ⟨e,p,head,kind⟩ := normal.copyable.head_exists
    have same := (MatchEmbedding.head_unique normal.head_at head).2
    exact same ▸ kind
  obtain ⟨k',h',W,other,free,g,same,primitive,owners,m,count⟩ := shallow_payload C cert closed label i source suffix
    (payload.matchEmbedding.primitive _ _ normal.head_at.1) kind
  have rel := normal.related other payload g same.symm
  refine ⟨k',h',W,other.copyable,free,rel.1,?_⟩
  intro e
  rcases normal.edge_cases e with rfl | rfl
  · rw [← same]
    exact owners _
  · rw [rel.2]
    exact owners _

/-- A remote actual copy either resolves entirely through retained owners, or
has a literal selected-spine occurrence in the original context ending at one
exact shallow copying input. All edges of its actual payload then belong to
that same hole; no assumption of isolated or disjoint context holes is made. -/
theorem match_cases {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {v : C.Vertex}
    (away : ¬ Entering C (.rewrite,v)) {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (matched : CopyRule.SuccessorMatch (C.expand L) (Net.Expansion.host C L v) V) :
    (Nonempty (Retained C L (matched.payload.edges matched.normal.head).1) ∧
      ∃ n, CopyTrace.Resolves C v (matched.payload.edges matched.normal.head).1 matched.normal.primitive n) ∨
    ∃ (hole : C.Edge) (name : Hole)
      (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
      (n : Nat) (orientation : Fin (n+1) → Bool)
      (spine : Occurrence (ContractionSpine.atDepth .term n orientation d) C),
      C.edgeLabel hole = primitiveLabel d (.hole name) ∧
      spine.ports (.input ⟨0,by simp⟩) = v ∧
      spine.ports (.output 0) = C.sourcePort hole i ∧
      (∀ e, (matched.payload.edges e).1 = hole) := by
  obtain ⟨cost,a,source,path,label,kind⟩ := matched.resolves
  have same := (C.expand L).source_unique source matched.head_at.2
  subst a
  obtain ⟨⟨initial⟩,head⟩ := BindingOverlap.head_retained C cert away matched.head_at
  have notHole (name) : C.edgeLabel matched.active.1 ≠ primitiveLabel d (.hole name) := by
    intro bad
    have impossible := primitiveLabel_injective d (head.1.symm.trans bad)
    cases impossible
  rcases trace_cases C cert path notHole with ⟨⟨last⟩,retained⟩ |
      ⟨hole,name,i,entry,last,n,l,holeLabel,input,pre,hop,target,suffix,total⟩
  · refine .inl ⟨⟨last⟩,cost,matched.active.1,head.2,retained,?_,kind⟩
    apply (last.primitive _).mp
    change (L (matched.payload.edges matched.normal.head).1).edgeLabel
      (matched.payload.edges matched.normal.head).2 = _ at label
    simpa only [last.only (matched.payload.edges matched.normal.head).2] using label
  · have terminal : Terminal (CopyTrace.Hop C) hole := by
      intro e next
      rcases next.1 with contr | weak
      all_goals
        have impossible := primitiveLabel_injective d (holeLabel.symm.trans (by assumption))
        cases impossible
    obtain ⟨orientation,spine,token,output,_,_⟩ := prefix_spine C pre hop terminal head.2 target
    obtain ⟨k',h',W,copyable,free,related,owners⟩ :=
      payload_owner C cert closed holeLabel i input matched.normal matched.payload suffix
    exact .inr ⟨hole,name,i,n,orientation,spine,holeLabel,token,output,owners⟩

end Hypernets.Copying.CopyingTemplate.Remote
