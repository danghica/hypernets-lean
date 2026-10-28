import Hypernets.Copying.ConverseHeadOrigin
import Hypernets.Copying.BindingStoreRewrite

/-! Converse store inspection follows the actual selected atom trace. The
original context owns its head, inspected instances, entire selected spine and
store; unrelated siblings in a supplied atom tree need not be retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Search.Expansion MatchEmbedding
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
include cert

omit cert in
/-- Retention exposes the complete ordered target row of the supplied edge. -/
theorem retained_target {a : (C.expand R).Edge} (copy : Retained C R a.1) :
    (C.expand R).target a = (C.target a.1).map (Net.Expansion.host C R) := by
  rcases a with ⟨a,x⟩
  simpa only [copy.only x] using copy.target_eq

omit cert in
/-- A retained atom-trace edge reflects its actual primitive and adjacency. -/
theorem store_hop_owner {a b : (C.expand R).Edge} (copy : Retained C R a.1)
    (hop : StoreTrace.Hop (C.expand R) a b) : StoreTrace.Hop C a.1 b.1 := by
  refine ⟨?_,BindingOverlap.adjacent_owner C copy hop.2⟩
  have reflect {p} (label : (C.expand R).edgeLabel a = primitiveLabel d p) :
      C.edgeLabel a.1 = primitiveLabel d p := by
    apply (copy.primitive p).mp
    change (R a.1).edgeLabel a.2 = _ at label
    simpa only [copy.only a.2] using label
  rcases hop.1 with label | label | label
  · exact .inl (reflect label)
  · exact .inr (.inl (reflect label))
  · exact .inr (.inr (reflect label))

/-- A selected atom spine after a binding source remains in the original
context, including its exact number of hops. -/
theorem store_trace_owner (free : BindingFree C) (start : C.Edge)
    (binding : BindingLabel d (C.edgeLabel start)) (source : ∃ v, v ∈ C.source start)
    {a b : (C.expand R).Edge} {n} (path : Trace (StoreTrace.Hop (C.expand R)) a b n)
    (initial : Nonempty (Retained C R a.1)) (ancestry : Ancestor C start a.1) :
    Trace (StoreTrace.Hop C) a.1 b.1 n := by
  induction path with
  | refl => exact .refl _
  | @step a b c n hop rest ih =>
    obtain ⟨copy⟩ := initial
    have reflected := store_hop_owner C copy hop
    obtain ⟨next,anc⟩ := BindingOverlap.ancestor_retained C (fun e => (cert e).converse)
      free.shallow start binding source (.step hop.2 (.refl _)) ⟨copy⟩ ancestry
    exact .step reflected (ih next anc)

/-- A sourced instance or atom contraction is binding; a weakening cannot
be selected as the source of an operation argument. -/
theorem store_start_binding {a b : (C.expand R).Edge}
    (copy : Retained C R a.1) (hop : StoreTrace.Hop (C.expand R) a b)
    (source : ∃ v, v ∈ (C.expand R).source a) : BindingLabel d (C.edgeLabel a.1) := by
  rcases (store_hop_owner C copy hop).1 with label | label | label
  · rw [label]; cases d <;> trivial
  · rw [label]; cases d <;> trivial
  · obtain ⟨v,member⟩ := source
    have sourceEmpty : (C.expand R).source a = [] := by
      have empty : C.source a.1 = [] := List.length_eq_zero_iff.mp (by
        rw [C.source_length,label,primitive_input]; rfl)
      have actual : (C.expand R).source a = (C.source a.1).map (Net.Expansion.host C R) := by
        rcases a with ⟨a,x⟩
        simpa only [copy.only x] using copy.source_eq
      rw [actual,empty]; rfl
    rw [sourceEmpty] at member
    exact False.elim (List.not_mem_nil member)

/-- Exact original operation-argument lookup is preserved together with the
selected store and its hop count. This handles cyclic surrounding stores. -/
theorem operand_owner {input v o j s n}
    (free : BindingFree C) (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (bound : j < o.arguments)
    (operand : StoreTrace.Operand (C.expand R) (Net.Expansion.host C R v) o j s n) :
    StoreTrace.Operand C v o j s.1 n ∧
      (∀ h, C.edgeLabel s.1 ≠ primitiveLabel d (.hole h)) := by
  obtain ⟨head,a,headAt,⟨w,arg,src⟩,trace,label⟩ := operand
  obtain ⟨⟨hc⟩,original⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away headAt
  have avoid := argument_source_not_hole C cert away rooted headAt bound arg src
  obtain ⟨_,ac⟩ := (cert a.1).retained_of_not_hole avoid
  have rt : (C.expand R).target head = (C.target head.1).map (Net.Expansion.host C R) := by
    rcases head with ⟨head,x⟩
    simpa only [hc.only x] using hc.target_eq
  rw [rt,List.getElem?_map] at arg
  obtain ⟨u,selected,eq⟩ := Option.map_eq_some_iff.mp arg
  have originalArg : Argument C head.1 j a.1 := ⟨u,selected,source_owner C R (eq ▸ src)⟩
  have traces : Trace (StoreTrace.Hop C) a.1 s.1 n ∧ Nonempty (Retained C R s.1) := by
    cases trace with
    | refl => exact ⟨.refl _,⟨ac⟩⟩
    | @step a b s n first rest =>
      have binding := store_start_binding C cert ac first ⟨w,src⟩
      have source : ∃ x, x ∈ C.source a.1 := ⟨u,source_owner C R (eq ▸ src)⟩
      exact ⟨store_trace_owner C cert free a.1 binding source (.step first rest) ⟨ac⟩ (.refl _),
        (BindingOverlap.ancestor_retained C (fun e => (cert e).converse) free.shallow a.1
          binding source (StoreTrace.ancestor (.step first rest)) ⟨ac⟩ (.refl _)).1⟩
  obtain ⟨path,⟨sc⟩⟩ := traces
  have store : C.edgeLabel s.1 = primitiveLabel d .store := by
    apply (sc.primitive .store).mp
    change (R s.1).edgeLabel s.2 = _ at label
    simpa only [sc.only s.2] using label
  refine ⟨⟨head.1,a.1,original,originalArg,path,store⟩,?_⟩
  intro h hole
  cases primitiveLabel_injective d (store.symm.trans hole)

/-- Retained right occurrences with the same original owner are the same
actual edge, preserving equality and disequality of store identities. -/
theorem owner_eq_iff {a b : (C.expand R).Edge}
    (avoid : ∀ h, C.edgeLabel a.1 ≠ primitiveLabel d (.hole h)) : a.1 = b.1 ↔ a = b := by
  refine ⟨?_,congrArg Sigma.fst⟩
  obtain ⟨_,copy⟩ := (cert a.1).retained_of_not_hole avoid
  rcases a with ⟨a,x⟩
  rcases b with ⟨b,y⟩
  intro same
  change a = b at same
  subst b
  exact congrArg (Sigma.mk a) ((copy.only x).trans (copy.only y).symm)

/-- Both argument traces and the resulting reference-identity decision already
hold in the common context, for equal as well as different stores. -/
theorem equality_owner {input v b}
    (free : BindingFree C) (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (decision : AtomEquality.Decision (C.expand R) (Net.Expansion.host C R v) b) :
    AtomEquality.Decision C v b := by
  obtain ⟨s,t,n,m,left,right,eq⟩ := decision
  obtain ⟨left,avoid⟩ := operand_owner C cert free away rooted (by decide) left
  obtain ⟨right,_⟩ := operand_owner C cert free away rooted (by decide) right
  exact ⟨s.1,t.1,n,m,left,right,(owner_eq_iff C cert avoid).trans eq⟩

/-- The actual read's head, store, contents and exact lookup count all belong
to one original-context match. -/
theorem read_match_owner {input v}
    (free : BindingFree C) (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (m : Dereference.Match (C.expand R) (Net.Expansion.host C R v)) :
    ∃ q : Dereference.Match C v, q.headEdge = m.headEdge.1 ∧ q.storeEdge = m.storeEdge.1 ∧
      q.count = m.count ∧ Net.Expansion.host C R q.contents = m.contents := by
  obtain ⟨operand,avoid⟩ := operand_owner C cert free away rooted (by decide) m.operand
  obtain ⟨_,head⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away m.head
  obtain ⟨_,copy⟩ := (cert m.storeEdge.1).retained_of_not_hole avoid
  have store : C.edgeLabel m.storeEdge.1 = primitiveLabel d .store := by
    apply (copy.primitive .store).mp
    have label := m.store
    change (R m.storeEdge.1).edgeLabel m.storeEdge.2 = _ at label
    simpa only [copy.only m.storeEdge.2] using label
  obtain ⟨u,eq⟩ := copy.target_origin (show m.contents ∈ (C.expand R).target m.storeEdge by
    rw [m.storeTarget]; exact List.mem_cons_self)
  have target : C.target m.storeEdge.1 = [u] := by
    apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C R eq)).mp
    have actual : (C.expand R).target m.storeEdge =
        (C.target m.storeEdge.1).map (Net.Expansion.host C R) := by
      exact retained_target C copy
    rw [← actual,m.storeTarget]
    exact congrArg (fun x => [x]) eq.symm
  exact ⟨⟨m.headEdge.1,m.storeEdge.1,u,m.count,head,store,target,operand⟩,rfl,rfl,rfl,eq⟩

/-- The actual write's selected store, ordered new-value wire and old-content
wire are all original-context coordinates, with no chosen tree presentation. -/
theorem assignment_match_owner {input v}
    (free : BindingFree C) (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (m : Assignment.Match (C.expand R) (Net.Expansion.host C R v)) :
    ∃ q : Assignment.Match C v, q.headEdge = m.headEdge.1 ∧ q.storeEdge = m.storeEdge.1 ∧
      q.count = m.count ∧ Net.Expansion.host C R q.instanceWire = m.instanceWire ∧
      Net.Expansion.host C R q.newValue = m.newValue ∧ Net.Expansion.host C R q.oldValue = m.oldValue := by
  obtain ⟨operand,avoid⟩ := operand_owner C cert free away rooted (by decide) m.operand
  obtain ⟨⟨hc⟩,head⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away m.head
  obtain ⟨_,sc⟩ := (cert m.storeEdge.1).retained_of_not_hole avoid
  have store : C.edgeLabel m.storeEdge.1 = primitiveLabel d .store := by
    apply (sc.primitive .store).mp
    have label := m.store
    change (R m.storeEdge.1).edgeLabel m.storeEdge.2 = _ at label
    simpa only [sc.only m.storeEdge.2] using label
  obtain ⟨a,aeq⟩ := hc.target_origin (show m.instanceWire ∈ (C.expand R).target m.headEdge by
    rw [m.targets]; exact List.mem_cons_self)
  obtain ⟨b,beq⟩ := hc.target_origin (show m.newValue ∈ (C.expand R).target m.headEdge by
    rw [m.targets]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨c,ceq⟩ := sc.target_origin (show m.oldValue ∈ (C.expand R).target m.storeEdge by
    rw [m.storeTarget]; exact List.mem_cons_self)
  have targets : C.target m.headEdge.1 = [a,b] := by
    apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C R eq)).mp
    have row : (C.expand R).target m.headEdge =
        (C.target m.headEdge.1).map (Net.Expansion.host C R) := by
      exact retained_target C hc
    rw [← row,m.targets]
    simp only [List.map_cons,List.map_nil,aeq,beq]
  have storeTarget : C.target m.storeEdge.1 = [c] := by
    apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C R eq)).mp
    have row : (C.expand R).target m.storeEdge =
        (C.target m.storeEdge.1).map (Net.Expansion.host C R) := by
      exact retained_target C sc
    rw [← row,m.storeTarget]
    exact congrArg (fun x => [x]) ceq.symm
  exact ⟨⟨m.headEdge.1,m.storeEdge.1,a,b,c,m.count,head,store,targets,storeTarget,operand⟩,
    rfl,rfl,rfl,aeq,beq,ceq⟩

end Hypernets.Copying.OperationalTemplates.ConverseOverlap
