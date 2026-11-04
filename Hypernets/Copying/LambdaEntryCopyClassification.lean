import Hypernets.Copying.LambdaEntryCopyTrace
import Hypernets.Copying.CopyingRemoteSpine

/-! Exhaustive actual copying overlap classification for lambda-entry
closed-output templates. The remote branch records an actual retained prefix,
its exact first shallow input, and the complete selected lambda payload. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryCopy
open Graph Opening Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries) (none : T.NoOutputs)
    (closed : HoleFree (C.expand L))
include cert heads none closed

/-- Any original normalized copy match is either entirely resolved at a
retained payload head, or enters one exact shallow family input through a
complete original selected spine. Entry is immediately the actual lambda
head, and every payload edge, including its full recursive box, has that owner. -/
theorem match_cases {v : C.Vertex} {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (matched : CopyRule.SuccessorMatch (C.expand L) (Net.Expansion.host C L v) V) :
    (Nonempty (Retained C L (matched.payload.edges matched.normal.head).1) ∧
      ∃ n, CopyTrace.Resolves C v (matched.payload.edges matched.normal.head).1 matched.normal.primitive n) ∨
    ∃ (hole : C.Edge) (name : Hole)
      (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
      (n : Nat) (orientation : Fin (n+1) → Bool)
      (spine : Occurrence (ContractionSpine.atDepth .term n orientation d) C),
      C.edgeLabel hole = primitiveLabel d (.hole name) ∧ T.Rel (L hole) (R hole) ∧
      spine.ports (.input ⟨0,by simp⟩) = v ∧
      spine.ports (.output 0) = C.sourcePort hole i ∧
      matched.payload.ports (.input 0) = Net.Expansion.host C L (C.sourcePort hole i) ∧
      matched.normal.primitive = .operation .lam ∧
      (∀ e, (matched.payload.edges e).1 = hole) := by
  obtain ⟨cost,a,source,path,label,kind⟩ := matched.resolves
  have same := (C.expand L).source_unique source matched.head_at.2
  subst a
  obtain ⟨initial⟩ := LambdaEntryOverlap.source_retained C cert heads matched.head_at.2 (by
    rw [matched.head_at.1]; intro eq; cases primitiveLabel_injective d eq)
  have original : MatchEmbedding.HeadAt C v matched.active.1 (.contraction .term) := by
    refine ⟨(initial.primitive _).mp ?_,source_owner C L matched.head_at.2⟩
    change (L matched.active.1).edgeLabel initial.edge = _
    exact (initial.only matched.active.2) ▸ matched.head_at.1
  have notHole (name) : C.edgeLabel matched.active.1 ≠ primitiveLabel d (.hole name) := by
    intro bad
    cases primitiveLabel_injective d (original.1.symm.trans bad)
  rcases trace_cases C cert path notHole with ⟨⟨last⟩,retained⟩ |
      ⟨hole,name,i,entry,last,n,l,holeLabel,input,pre,hop,target,suffix,total⟩
  · refine .inl ⟨⟨last⟩,cost,matched.active.1,original.2,retained,?_,kind⟩
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
    obtain ⟨orientation,spine,token,output,_,_⟩ :=
      CopyingTemplate.Remote.prefix_spine C pre hop terminal original.2 target
    obtain ⟨count,primitive,owners⟩ := shallow_payload_owner C cert heads none closed
      holeLabel i input matched.normal matched.payload suffix
    have zeroEq {a b : (C.expand L).Edge} (p : Trace (CopyTrace.Hop (C.expand L)) a b 0) : a = b := by
      cases p; rfl
    have sameHead := zeroEq (count ▸ suffix)
    have entered : Net.Expansion.host C L (C.sourcePort hole i) ∈
        (C.expand L).source ⟨hole,entry⟩ := List.mem_map_of_mem input
    rw [sameHead,← matched.payload.source,matched.normal.head_source] at entered
    have point : matched.payload.ports (.input 0) = Net.Expansion.host C L (C.sourcePort hole i) :=
      (List.mem_singleton.mp entered).symm
    exact .inr ⟨hole,name,i,n,orientation,spine,holeLabel,
      (cert hole).relation_at_hole holeLabel closed,token,output,point,primitive,owners⟩

end Hypernets.Copying.LambdaEntryCopy
