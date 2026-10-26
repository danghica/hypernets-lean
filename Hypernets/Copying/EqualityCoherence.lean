import Hypernets.Copying.EqualityDifferentReplacement

/-! Successor coherence for all contextual reference-identity comparisons. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- An actual comparison rewrite has a concrete store-identity decision. -/
theorem rewrite_equality_decision {d I O} {G H : Hypernet d I O} {v w e}
    (step : Rewrite G v H w) (head : HeadAt G v e (.operation (.binary .atomEq))) :
    ∃ b, AtomEquality.Decision G v b := by
  obtain ⟨c,a,chosen,data⟩ := rewrite_recognizes step
  have eq := (head_unique chosen head).2
  cases c <;> simp only [Choice.head] at eq <;> try cases eq
  · exact ⟨_,data⟩
  · rename_i o m n
    cases o <;> cases eq

/-- A comparison decision and its head reflect into the changed component of a real match. -/
theorem rewrite_equality_reflect {d r I O J K} {G H : Hypernet d I O} {N : Hypernet r J K}
    {v w a b} (step : Rewrite G v H w) (f : MatchEmbedding G N)
    (head : HeadAt N (f.ports v) a (.operation (.binary .atomEq)))
    (decision : AtomEquality.Decision N (f.ports v) b) :
    ∃ e, HeadAt G v e (.operation (.binary .atomEq)) ∧ f.edges e = a ∧ AtomEquality.Decision G v b := by
  obtain ⟨e,inner,eq⟩ := rewrite_head_reflect step f head
  obtain ⟨c,hc⟩ := rewrite_equality_decision step inner
  have same := AtomEquality.decision_unique (AtomEquality.decision_map f hc) decision
  exact ⟨e,inner,eq,same ▸ hc⟩

/-- Both original local comparison rules produce the source-determined canonical graph. -/
theorem local_equality_canonical {d I O} {G H : Hypernet d I O} {v w e b}
    (step : Local G v H w) (head : HeadAt G v e (.operation (.binary .atomEq)))
    (decision : AtomEquality.Decision G v b) :
    Nonempty (StateIso (AtomEquality.canonical G e head.1 v b) ⟨H,(.search,w)⟩) := by
  cases step with
  | allocate A stable => cases (head_unique head (Allocation.head_at A)).2
  | read T d =>
    have bad := (head_unique head (show HeadAt (Dereference.before T d) _ ⟨.reader,(0 : Fin 1)⟩
      (.operation (.unary .deref)) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | @assign d h O T A stable =>
    cases d
    all_goals
      have bad := (head_unique head (show HeadAt (Assignment.before T A) _ ⟨.assign,(0 : Fin 1)⟩
        (.operation (.binary .assign)) from ⟨rfl,List.mem_cons_self⟩)).2
      cases bad
  | same T d =>
    have eq := (head_unique head (AtomEquality.Same.head_at T d)).1
    have result := AtomEquality.decision_unique decision (AtomEquality.Same.before_decision T d)
    subst e; subst b
    exact ⟨AtomEquality.Same.canonical_local T d⟩
  | different T U d =>
    have eq := (head_unique head (AtomEquality.Different.head_at T U d)).1
    have result := AtomEquality.decision_unique decision (AtomEquality.Different.before_decision T U d)
    subst e; subst b
    exact ⟨AtomEquality.Different.canonical_local T U d⟩
  | beta B A stable =>
    have bad := (head_unique head (show HeadAt (Application.before B A) _ ⟨false,(0 : Fin 1)⟩
      (.operation .app) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | copy T A copyable =>
    obtain ⟨a,chosen⟩ := CopyRule.before_active_head T A ⟨0,by simp⟩
    cases (head_unique head chosen).2
  | unaryArithmetic d n => cases (head_unique head (Arithmetic.unary_head d n)).2
  | binaryArithmetic o d m n =>
    have bad := (head_unique head (Arithmetic.binary_head o d m n)).2
    cases o <;> cases bad

/-- Arbitrary context decompositions of a comparison preserve the same complete successor. -/
theorem rewrite_equality_canonical {d I O} {G H : Hypernet d I O} {v w e b}
    (step : Rewrite G v H w) (head : HeadAt G v e (.operation (.binary .atomEq)))
    (decision : AtomEquality.Decision G v b) :
    Nonempty (StateIso (AtomEquality.canonical G e head.1 v b) ⟨H,(.search,w)⟩) := by
  induction step with
  | «local» step => exact local_equality_canonical step head decision
  | @rename I O G H G' H' v w f g step ih =>
    obtain ⟨a,inner,eq,data⟩ := rewrite_equality_reflect step (MatchEmbedding.ofDeepIso f) head decision
    obtain ⟨result⟩ := ih inner data
    subst e
    exact ⟨(AtomEquality.canonical_rename f a inner.1 v b).symm.trans
      (result.trans ⟨g,rfl,rfl⟩)⟩
  | @plug I O C hole G H v w step ih =>
    obtain ⟨a,inner,eq,data⟩ := rewrite_equality_reflect step (MatchEmbedding.plug C hole G) head decision
    obtain ⟨result⟩ := ih inner data
    subst e
    exact ⟨(Replacement.plug C hole G a (AtomEquality.filler G a inner.1 b) v).trans
      (StateIso.plug C hole result)⟩
  | @expand I O C F K hole others v w step ih =>
    obtain ⟨a,inner,eq,data⟩ := rewrite_equality_reflect step (MatchEmbedding.expand C F hole) head decision
    obtain ⟨result⟩ := ih inner data
    subst e
    exact ⟨Replacement.expand_result C F K hole others a (AtomEquality.filler (F hole) a inner.1 b) v w result⟩

/-- Any two actual rewrites at a comparison request have isomorphic successor states.
No decision or machine-determinism assumption is required: the first rewrite supplies it. -/
theorem equality_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u e}
    (head : HeadAt G v e (.operation (.binary .atomEq)))
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  obtain ⟨b,data⟩ := rewrite_equality_decision first head
  obtain ⟨f⟩ := rewrite_equality_canonical first head data
  obtain ⟨g⟩ := rewrite_equality_canonical second head data
  exact ⟨f.symm.trans g⟩
end Hypernets.Copying.Combined

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- Reference comparison is deterministic up to recursive state representation in the full machine. -/
theorem equality_step_deterministic {d I O} {G : Hypernet d I O} {v e} {s t : State d I O}
    (head : HeadAt G v e (.operation (.binary .atomEq)))
    (first : Step ⟨G,(.rewrite,v)⟩ s) (second : Step ⟨G,(.rewrite,v)⟩ t) :
    Nonempty (StateIso s t) := by
  cases first with
  | search _ h => exact False.elim (Search.no_rewrite h)
  | rewrite first =>
    cases second with
    | search _ h => exact False.elim (Search.no_rewrite h)
    | rewrite second => exact equality_rewrite_deterministic head first second

/-- Comparison consumes one transition with the same future successful costs for every match. -/
theorem equality_cost_spectrum {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation (.binary .atomEq)))
    (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn n ⟨G,(.rewrite,v)⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => equality_step_deterministic head h step) n

/-- Unbounded comparison successors agree as complete represented states. -/
theorem equality_unbounded_deterministic {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation (.binary .atomEq)))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    Represents s t := by
  cases first with
  | lift first =>
    cases second with
    | lift second =>
      obtain ⟨iso⟩ := equality_step_deterministic head first second
      exact .lift iso

/-- Comparison-successor equivalence holds at every cost preorder, including exact costs. -/
theorem equality_unbounded_equiv (Q : CostOrder) {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation (.binary .atomEq)))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    unboundedMachine.Equiv Q s t := represents_equiv Q (equality_unbounded_deterministic head first second)
end Hypernets.Copying.Combined
