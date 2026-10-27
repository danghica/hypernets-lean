import Hypernets.Copying.CopySuccessorExpansion

/-! Complete copying coherence for independent contextual matches of the original rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Combined
inductive SuccessorWitness : {d : Nat} → {I O : List Wire} → (G K : Hypernet d I O) → G.Vertex → K.Vertex → Prop where
  | certificate {d I O k h} {G K : Hypernet d I O} {v w}
      {H : Hypernet d [.term] (environmentInterface k h)}
      (a : SuccessorCertificate G K v w H) : SuccessorWitness G K v w

theorem SuccessorWitness.coherent {d I O} {G H K : Hypernet d I O} {v w u}
    (a : SuccessorWitness G H v w) (b : SuccessorWitness G K v u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  cases a with
  | certificate a => cases b with
    | certificate b => exact a.coherent b

theorem local_witness {d n k h} (T : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable H) :
    SuccessorWitness (before T H) (after T H) (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) := by
  obtain ⟨K,⟨normal⟩,⟨iso⟩⟩ := normal_form copyable
  exact .certificate ((local_certificate T normal).rename (before_congr (Net.Iso.refl _) iso.symm)
    (after_congr (Net.Iso.refl _) iso.symm))
end Hypernets.Copying.CopyRule

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding CopyRule

theorem rewrite_head_exists_reflect {d r I O J K} {G H : Hypernet d I O} {N : Hypernet r J K} {v w p}
    (step : Rewrite G v H w) (f : MatchEmbedding G N) (head : ∃ e, HeadAt N (f.ports v) e p) :
    ∃ e, HeadAt G v e p := by
  obtain ⟨c,e,chosen,_⟩ := rewrite_recognizes step
  obtain ⟨a,head⟩ := head
  have same := (head_unique (f.head chosen) head).2
  exact ⟨e,same ▸ chosen⟩

theorem local_copy_certificate {d I O} {G H : Hypernet d I O} {v w}
    (step : Local G v H w) (head : ∃ e, HeadAt G v e (.contraction .term)) : SuccessorWitness G H v w := by
  obtain ⟨e,head⟩ := head
  cases step with
  | copy T H copyable => exact local_witness T copyable
  | allocate G stable => cases (head_unique head (Allocation.head_at G)).2
  | read T d => cases (head_unique head (Dereference.localMatch T d).head).2
  | assign T G stable => cases (head_unique head (Assignment.localMatch T G).head).2
  | same T d => cases (head_unique head (AtomEquality.Same.head_at T d)).2
  | different T U d => cases (head_unique head (AtomEquality.Different.head_at T U d)).2
  | beta B G stable => cases (head_unique head (Application.localMatch B G).head_at).2
  | unaryArithmetic d n => cases (head_unique head (Arithmetic.unary_head d n)).2
  | binaryArithmetic o d m n => cases (head_unique head (Arithmetic.binary_head o d m n)).2

/-- Every actual copying rewrite supplies the complete certificate, with no extra operational premise. -/
theorem rewrite_copy_certificate {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) (head : ∃ e, HeadAt G v e (.contraction .term)) : SuccessorWitness G H v w := by
  induction step with
  | «local» step => exact local_copy_certificate step head
  | rename f g step ih =>
    have witness := ih (rewrite_head_exists_reflect step (MatchEmbedding.ofDeepIso f) head)
    cases witness with
    | certificate a => exact .certificate (a.rename f g)
  | plug C hole step ih =>
    have witness := ih (rewrite_head_exists_reflect step (MatchEmbedding.plug C hole _) head)
    cases witness with
    | certificate a => exact .certificate (a.plug C hole)
  | expand C F K hole others step ih =>
    have witness := ih (rewrite_head_exists_reflect step (MatchEmbedding.expand C F hole) head)
    cases witness with
    | certificate a => exact .certificate (a.expand C F K hole others)

/-- Neither the tree boundary nor the payload representation affects the complete successor. -/
theorem copying_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u e}
    (head : HeadAt G v e (.contraction .term)) (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) :=
  (rewrite_copy_certificate first ⟨e,head⟩).coherent (rewrite_copy_certificate second ⟨e,head⟩)

/-- Every pair of actual contextual rewrites has recursively isomorphic complete results. -/
theorem rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u}
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  rcases rewrite_coherent_or_copying first second with coherent | ⟨e,head⟩
  · exact coherent
  · exact copying_rewrite_deterministic head first second

/-- Successor determinism up to recursive representation for the entire original combined machine. -/
theorem step_deterministic {d I O} {s t u : State d I O} (first : Step s t) (second : Step s u) :
    Nonempty (StateIso t u) := by
  cases first with
  | search G h => exact ⟨StateIso.ofEq (search_successor_unique h second).symm⟩
  | rewrite first => cases second with
    | search G h => exact False.elim (Search.no_rewrite h)
    | rewrite second => exact rewrite_deterministic first second

theorem cost_spectrum {d I O} {s t : State d I O} (step : Step s t) (n : Nat) :
    TerminatesIn n s ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => step_deterministic h step) n

theorem unbounded_deterministic {s t u : UnboundedState} (first : UnboundedStep s t) (second : UnboundedStep s u) :
    Represents t u := by
  cases first with
  | lift first => cases second with
    | lift second => obtain ⟨iso⟩ := step_deterministic first second; exact .lift iso

theorem unbounded_successors_equiv (Q : CostOrder) {s t u : UnboundedState}
    (first : UnboundedStep s t) (second : UnboundedStep s u) : unboundedMachine.Equiv Q t u :=
  represents_equiv Q (unbounded_deterministic first second)
end Hypernets.Copying.Combined
