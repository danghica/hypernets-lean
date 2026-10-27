import Hypernets.Copying.ApplicationOpeningExpansion

/-! Application successor coherence for the original contextual copying UAM. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph Combined

/-- Existentially records the depth and interface of the actual opened box. -/
inductive OpeningWitness : {d : Nat} → {I O : List Wire} → (G H : Hypernet d I O) → G.Vertex → H.Vertex → Prop where
  | certificate {d I O k h} {G H : Hypernet (d+1) I O} {v w}
      {B : Hypernet d [.term] (environmentInterface (k+1) h)}
      (a : OpeningCertificate G H v w B) : OpeningWitness G H v w

theorem OpeningWitness.coherent {d I O} {G H K : Hypernet d I O} {v w u}
    (a : OpeningWitness G H v w) (b : OpeningWitness G K v u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  cases a with
  | certificate a => cases b with
    | certificate b => exact a.coherent b
end Hypernets.Copying.Application

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding Application

/-- Local beta is the only compute rule with an application head. -/
theorem local_application_certificate {d I O} {G H : Hypernet d I O} {v w}
    (step : Local G v H w) (recognized : Recognizes G v .beta) : OpeningWitness G H v w := by
  obtain ⟨e,head,_⟩ := recognized
  cases step with
  | beta B G stable => exact .certificate (local_certificate B G)
  | unaryArithmetic d n =>
    have bad := (head_unique head (Arithmetic.unary_head d n)).2
    cases bad
  | binaryArithmetic o d m n =>
    have bad := (head_unique head (Arithmetic.binary_head o d m n)).2
    cases o <;> cases bad
  | allocate G stable =>
    have bad := (head_unique head (Allocation.head_at G)).2
    cases bad
  | read T d =>
    have bad := (head_unique head (Dereference.localMatch T d).head).2
    cases bad
  | assign T G stable =>
    have bad := (head_unique head (Assignment.localMatch T G).head).2
    cases bad
  | same T d =>
    have bad := (head_unique head (AtomEquality.Same.head_at T d)).2
    cases bad
  | different T U d =>
    have bad := (head_unique head (AtomEquality.Different.head_at T U d)).2
    cases bad
  | copy T G copyable =>
    obtain ⟨h,chosen⟩ := CopyRule.before_active_head T G ⟨0,by simp⟩
    have bad := (head_unique head chosen).2
    cases bad

/-- Every actual application rewrite yields a complete opening certificate.
No determinism or template assumptions are premises of this theorem. -/
theorem rewrite_application_certificate {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) (recognized : Recognizes G v .beta) : OpeningWitness G H v w := by
  induction step with
  | «local» step => exact local_application_certificate step recognized
  | rename f g step ih =>
    have witness := ih (rewrite_recognition_reflect step (MatchEmbedding.ofDeepIso f) recognized)
    cases witness with
    | certificate a => exact .certificate (a.rename f g)
  | plug C hole step ih =>
    have witness := ih (rewrite_recognition_reflect step (MatchEmbedding.plug C hole _) recognized)
    cases witness with
    | certificate a => exact .certificate (a.plug C hole)
  | expand C F K hole others step ih =>
    have witness := ih (rewrite_recognition_reflect step (MatchEmbedding.expand C F hole) recognized)
    cases witness with
    | certificate a => exact .certificate (a.expand C F K hole others)

/-- Independently matched applications have recursively isomorphic entire successors. -/
theorem application_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u e}
    (head : HeadAt G v e (.operation .app)) (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) :=
  (rewrite_application_certificate first ⟨e,head,trivial⟩).coherent
    (rewrite_application_certificate second ⟨e,head,trivial⟩)

theorem application_step_deterministic {d I O} {G : Hypernet d I O} {v e} {s t : State d I O}
    (head : HeadAt G v e (.operation .app))
    (first : Step ⟨G,(.rewrite,v)⟩ s) (second : Step ⟨G,(.rewrite,v)⟩ t) : Nonempty (StateIso s t) := by
  cases first with
  | search _ h => exact False.elim (Search.no_rewrite h)
  | rewrite first => cases second with
    | search _ h => exact False.elim (Search.no_rewrite h)
    | rewrite second => exact application_rewrite_deterministic head first second

theorem application_cost_spectrum {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation .app)) (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn n ⟨G,(.rewrite,v)⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => application_step_deterministic head h step) n

theorem application_unbounded_deterministic {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation .app))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) : Represents s t := by
  cases first with
  | lift first => cases second with
    | lift second =>
      obtain ⟨iso⟩ := application_step_deterministic head first second
      exact .lift iso

theorem application_unbounded_equiv (Q : CostOrder) {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation .app))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    unboundedMachine.Equiv Q s t := represents_equiv Q (application_unbounded_deterministic head first second)
end Hypernets.Copying.Combined
