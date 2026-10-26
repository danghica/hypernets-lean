import Hypernets.Copying.AssignmentReplacement

/-! Complete contextual assignment coherence, with the original stable-value requirement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- Each actual local write has the canonical complete successor. -/
theorem local_assignment_canonical {d I O} {G H : Hypernet d I O} {v w}
    (step : Local G v H w) (m : Assignment.Match G v) :
    Nonempty (StateIso m.canonical ⟨H,(.search,w)⟩) := by
  cases step with
  | allocate A stable => cases (head_unique m.head (Allocation.head_at A)).2
  | read T d =>
    have bad := (head_unique m.head (show HeadAt (Dereference.before T d) _ ⟨.reader,(0 : Fin 1)⟩
      (.operation (.unary .deref)) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | @assign d h O T A stable =>
    have eq := Assignment.Match.unique m (Assignment.localMatch T A)
    rw [eq]
    exact ⟨Assignment.Replacement.canonical_local T A⟩
  | same T d => cases (head_unique m.head (AtomEquality.Same.head_at T d)).2
  | different T U d => cases (head_unique m.head (AtomEquality.Different.head_at T U d)).2
  | beta B A stable =>
    have bad := (head_unique m.head (show HeadAt (Application.before B A) _ ⟨false,(0 : Fin 1)⟩
      (.operation .app) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | copy T A copyable =>
    obtain ⟨a,chosen⟩ := CopyRule.before_active_head T A ⟨0,by simp⟩
    cases (head_unique m.head chosen).2
  | unaryArithmetic d n => cases (head_unique m.head (Arithmetic.unary_head d n)).2
  | binaryArithmetic o d left right =>
    have bad := (head_unique m.head (Arithmetic.binary_head o d left right)).2
    cases o <;> cases bad


/-- Write data comes from the actual local rule, not an assumed matching oracle. -/
theorem local_assignment_match {d I O} {G H : Hypernet d I O} {v w e}
    (step : Local G v H w) (head : HeadAt G v e (.operation (.binary .assign))) :
    Nonempty (Assignment.Match G v) := by
  cases step with
  | allocate A stable => cases (head_unique head (Allocation.head_at A)).2
  | read T d =>
    have bad := (head_unique head (show HeadAt (Dereference.before T d) _ ⟨.reader,(0 : Fin 1)⟩
      (.operation (.unary .deref)) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | @assign d h O T A stable => exact ⟨Assignment.localMatch T A⟩
  | same T d => cases (head_unique head (AtomEquality.Same.head_at T d)).2
  | different T U d => cases (head_unique head (AtomEquality.Different.head_at T U d)).2
  | beta B A stable =>
    have bad := (head_unique head (show HeadAt (Application.before B A) _ ⟨false,(0 : Fin 1)⟩
      (.operation .app) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | copy T A copyable =>
    obtain ⟨a,chosen⟩ := CopyRule.before_active_head T A ⟨0,by simp⟩
    cases (head_unique head chosen).2
  | unaryArithmetic d n => cases (head_unique head (Arithmetic.unary_head d n)).2
  | binaryArithmetic o d left right =>
    have bad := (head_unique head (Arithmetic.binary_head o d left right)).2
    cases o <;> cases bad


/-- Every contextual assignment rewrite exposes a unique source match. -/
theorem rewrite_assignment_match {d I O} {G H : Hypernet d I O} {v w e}
    (step : Rewrite G v H w) (head : HeadAt G v e (.operation (.binary .assign))) :
    Nonempty (Assignment.Match G v) := by
  induction step with
  | «local» step => exact local_assignment_match step head
  | rename f g step ih =>
    obtain ⟨a,inner,_⟩ := rewrite_head_reflect step (MatchEmbedding.ofDeepIso f) head
    obtain ⟨m⟩ := ih inner
    exact ⟨m.map (MatchEmbedding.ofDeepIso f)⟩
  | plug C hole step ih =>
    obtain ⟨a,inner,_⟩ := rewrite_head_reflect step (MatchEmbedding.plug C hole _) head
    obtain ⟨m⟩ := ih inner
    exact ⟨m.map (MatchEmbedding.plug C hole _)⟩
  | expand C F K hole others step ih =>
    obtain ⟨a,inner,_⟩ := rewrite_head_reflect step (MatchEmbedding.expand C F hole) head
    obtain ⟨m⟩ := ih inner
    exact ⟨m.map (MatchEmbedding.expand C F hole)⟩

/-- Every decomposition of an actual write yields the same source-determined complete graph. -/
theorem rewrite_assignment_canonical {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) (m : Assignment.Match G v) :
    Nonempty (StateIso m.canonical ⟨H,(.search,w)⟩) := by
  induction step with
  | «local» step => exact local_assignment_canonical step m
  | rename f g step ih =>
    obtain ⟨a,inner,_⟩ := rewrite_head_reflect step (MatchEmbedding.ofDeepIso f) m.head
    obtain ⟨z⟩ := rewrite_assignment_match step inner
    have eq := Assignment.Match.unique (z.map (MatchEmbedding.ofDeepIso f)) m
    rw [← eq]
    obtain ⟨result⟩ := ih z
    exact ⟨(z.canonical_rename f).symm.trans (result.trans ⟨g,rfl,rfl⟩)⟩
  | plug C hole step ih =>
    obtain ⟨a,inner,_⟩ := rewrite_head_reflect step (MatchEmbedding.plug C hole _) m.head
    obtain ⟨z⟩ := rewrite_assignment_match step inner
    have eq := Assignment.Match.unique (z.map (MatchEmbedding.plug C hole _)) m
    rw [← eq]
    obtain ⟨result⟩ := ih z
    exact ⟨(z.canonical_plug C hole).trans (StateIso.plug C hole result)⟩
  | expand C F K hole others step ih =>
    obtain ⟨a,inner,_⟩ := rewrite_head_reflect step (MatchEmbedding.expand C F hole) m.head
    obtain ⟨z⟩ := rewrite_assignment_match step inner
    have eq := Assignment.Match.unique (z.map (MatchEmbedding.expand C F hole)) m
    rw [← eq]
    obtain ⟨result⟩ := ih z
    exact ⟨z.canonical_expand_result C F K hole others result⟩

/-- Two actual writes from the same assignment request have isomorphic complete successor states. -/
theorem assignment_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u e}
    (head : HeadAt G v e (.operation (.binary .assign)))
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  obtain ⟨m⟩ := rewrite_assignment_match first head
  obtain ⟨f⟩ := rewrite_assignment_canonical first m
  obtain ⟨g⟩ := rewrite_assignment_canonical second m
  exact ⟨f.symm.trans g⟩

/-- Assignment is deterministic up to recursive state representation in the full machine. -/
theorem assignment_step_deterministic {d I O} {G : Hypernet d I O} {v e} {s t : State d I O}
    (head : HeadAt G v e (.operation (.binary .assign)))
    (first : Step ⟨G,(.rewrite,v)⟩ s) (second : Step ⟨G,(.rewrite,v)⟩ t) :
    Nonempty (StateIso s t) := by
  cases first with
  | search _ h => exact False.elim (Search.no_rewrite h)
  | rewrite first =>
    cases second with
    | search _ h => exact False.elim (Search.no_rewrite h)
    | rewrite second => exact assignment_rewrite_deterministic head first second

/-- Assignment consumes one transition with the same future successful costs for every match. -/
theorem assignment_cost_spectrum {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation (.binary .assign)))
    (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn n ⟨G,(.rewrite,v)⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => assignment_step_deterministic head h step) n

/-- Unbounded assignment successors agree as complete represented states. -/
theorem assignment_unbounded_deterministic {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation (.binary .assign)))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    Represents s t := by
  cases first with
  | lift first =>
    cases second with
    | lift second =>
      obtain ⟨iso⟩ := assignment_step_deterministic head first second
      exact .lift iso

/-- Assignment-successor equivalence holds at every cost preorder, including exact costs. -/
theorem assignment_unbounded_equiv (Q : CostOrder) {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation (.binary .assign)))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    unboundedMachine.Equiv Q s t := represents_equiv Q (assignment_unbounded_deterministic head first second)
end Hypernets.Copying.Combined
