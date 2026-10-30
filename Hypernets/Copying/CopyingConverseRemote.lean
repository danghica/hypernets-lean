import Hypernets.Copying.CopyingRightPayload
import Hypernets.Copying.CopyingTemplateRemoteClassification

/-! Every actual converse copy has either a wholly retained selected spine
or a first literal shallow copying input. The right distinguished input's
zero-length payload suffix is included explicitly. Contexts are unrestricted. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteRight
open Graph Opening Search.Expansion Remote

/-- Split the original right path at its first shallow component, retaining
the exact ordered input and all counted original-context prefix edges. -/
theorem trace_cases {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    {a b : (C.expand R).Edge} {n}
    (path : Trace (CopyTrace.Hop (C.expand R)) a b n)
    (initial : ∀ h, C.edgeLabel a.1 ≠ primitiveLabel d (.hole h)) :
    (Nonempty (Retained C R b.1) ∧ Trace (CopyTrace.Hop C) a.1 b.1 n) ∨
      FirstShallow C R a b n := by
  induction path with
  | refl =>
    obtain ⟨_,copy⟩ := (cert _).retained_of_not_hole initial
    exact .inl ⟨⟨copy⟩,.refl _⟩
  | @step a b c n hop tail ih =>
    obtain ⟨_,copy⟩ := (cert a.1).retained_of_not_hole initial
    have original := BindingOverlap.copying_hop_owner C copy hop
    by_cases next : ∃ h, C.edgeLabel b.1 = primitiveLabel d (.hole h)
    · obtain ⟨name,label⟩ := next
      obtain ⟨w,target,source⟩ := hop.2
      obtain ⟨v,eq⟩ := copy.target_origin target
      obtain ⟨i,mem,attached⟩ := source_input_exact C (eq ▸ source)
      have originalTarget : v ∈ C.target a.1 := target_owner C R (eq ▸ target)
      exact .inr ⟨b.1,name,i,b.2,a.1,0,n,label,mem,.refl _,original,
        attached ▸ originalTarget,tail,by omega⟩
    · have notHole : ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
        intro h eq; exact next ⟨h,eq⟩
      rcases ih notHole with ⟨last,rest⟩ | ⟨hole,name,i,entry,last,k,l,label,source,pre,hop,attached,suffix,total⟩
      · exact .inl ⟨last,.step original rest⟩
      · exact .inr ⟨hole,name,i,entry,last,k+1,l,label,source,.step original pre,hop,attached,suffix,by omega⟩

/-- Resolving from any original right hole input reaches that component's
actual complete payload, including a possible zero-hop distinguished suffix. -/
theorem shallow_payload {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {hole : C.Edge} {name}
    (label : C.edgeLabel hole = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    {entry : (R hole).Edge} (source : Port.input i ∈ (R hole).source entry)
    {last : (C.expand R).Edge} {n p}
    (suffix : Trace (CopyTrace.Hop (C.expand R)) ⟨hole,entry⟩ last n)
    (lastLabel : (C.expand R).edgeLabel last = primitiveLabel d p)
    (kind : CopyTrace.PayloadHead p) :
    ∃ k h, ∃ V : Hypernet d [.term] (environmentInterface k h),
      ∃ normal : CopyRule.NormalForm V, FocusFree V ∧
      ∃ payload : Occurrence V (C.expand R),
        payload.edges normal.head = last ∧ normal.primitive = p ∧
        (∀ e, (payload.edges e).1 = hole) := by
  have pair : Pair (L hole) (R hole) := (cert hole).converse.relation_at_hole label closed
  obtain ⟨k,h,V,normal,free,payload,m,resolve⟩ := pair.right_input_payload i
  let expanded := payload.comp (Occurrence.expand C R hole)
  have canonical := CopyTrace.resolves_map (MatchEmbedding.expand C R hole) resolve
  have actual : CopyTrace.Resolves (C.expand R)
      (Net.Expansion.insert C R hole (.input i)) last p n :=
    ⟨⟨hole,entry⟩,List.mem_map_of_mem source,suffix,lastLabel,kind⟩
  have same := CopyTrace.resolves_unique canonical actual
  exact ⟨k,h,V,normal,free,expanded,same.1,same.2.1,fun _ => rfl⟩

/-- The full independently supplied matched payload has the original entered
hole owner; recursive lambda bodies are retained without restriction. -/
theorem payload_owner {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {hole : C.Edge} {name}
    (label : C.edgeLabel hole = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    {entry : (R hole).Edge} (source : Port.input i ∈ (R hole).source entry)
    {k h} {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand R)) {n}
    (suffix : Trace (CopyTrace.Hop (C.expand R)) ⟨hole,entry⟩ (payload.edges normal.head) n) :
    ∃ k' h', ∃ W : Hypernet d [.term] (environmentInterface k' h'),
      Copyable W ∧ FocusFree W ∧ CopyRule.PayloadRelated V W ∧
      (∀ e, (payload.edges e).1 = hole) := by
  have kind : CopyTrace.PayloadHead normal.primitive := by
    obtain ⟨e,p,head,kind⟩ := normal.copyable.head_exists
    have same := (MatchEmbedding.head_unique normal.head_at head).2
    exact same ▸ kind
  obtain ⟨k',h',W,other,free,g,same,primitive,owners⟩ := shallow_payload C cert closed label i source suffix
    (payload.matchEmbedding.primitive _ _ normal.head_at.1) kind
  have rel := normal.related other payload g same.symm
  refine ⟨k',h',W,other.copyable,free,rel.1,?_⟩
  intro e
  rcases normal.edge_cases e with rfl | rfl
  · rw [← same]
    exact owners _
  · rw [rel.2]
    exact owners _

/-- Exhaustive converse first-entry classification for the actual supplied
copying match. The selected upstream prefix is a complete finite occurrence
in the original context and ends at the exact original hole input. -/
theorem match_cases {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {v : C.Vertex}
    (away : ¬ Entering C (.rewrite,v)) {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (matched : CopyRule.SuccessorMatch (C.expand R) (Net.Expansion.host C R v) V) :
    (Nonempty (Retained C R (matched.payload.edges matched.normal.head).1) ∧
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
  have same := (C.expand R).source_unique source matched.head_at.2
  subst a
  obtain ⟨⟨initial⟩,head⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away matched.head_at
  have notHole (name) : C.edgeLabel matched.active.1 ≠ primitiveLabel d (.hole name) := by
    intro bad
    have impossible := primitiveLabel_injective d (head.1.symm.trans bad)
    cases impossible
  rcases trace_cases C cert path notHole with ⟨⟨last⟩,retained⟩ |
      ⟨hole,name,i,entry,last,n,l,holeLabel,input,pre,hop,target,suffix,total⟩
  · refine .inl ⟨⟨last⟩,cost,matched.active.1,head.2,retained,?_,kind⟩
    apply (last.primitive _).mp
    change (R (matched.payload.edges matched.normal.head).1).edgeLabel
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

end Hypernets.Copying.CopyingTemplate.RemoteRight
