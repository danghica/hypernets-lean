import Hypernets.Copying.ApplicationCoherence

/-! Copying is the sole remaining family in complete successor coherence. -/
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- Two actual rewrites agree up to recursive state isomorphism unless their
common head is a term contraction. This classifies the original full machine. -/
theorem rewrite_coherent_or_copying {d I O} {G H K : Hypernet d I O} {v w u}
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) ∨ ∃ e, HeadAt G v e (.contraction .term) := by
  rcases rewrite_coherent_or_higherOrder first second with coherent | higher
  · exact .inl coherent
  · cases higher with
    | application head => exact .inl (application_rewrite_deterministic head first second)
    | copying head => exact .inr ⟨_,head⟩

theorem step_coherent_or_copying {d I O} {s t u : State d I O}
    (first : Step s t) (second : Step s u) :
    Nonempty (StateIso t u) ∨ (s.2.1 = .rewrite ∧ ∃ e, HeadAt s.1 s.2.2 e (.contraction .term)) := by
  cases first with
  | search G h => exact .inl ⟨StateIso.ofEq (search_successor_unique h second).symm⟩
  | rewrite first => cases second with
    | search G h => exact False.elim (Search.no_rewrite h)
    | rewrite second =>
      rcases rewrite_coherent_or_copying first second with coherent | copying
      · exact .inl coherent
      · exact .inr ⟨rfl,copying⟩

theorem step_deterministic_away_copying {d I O} {s t u : State d I O}
    (outside : ¬ (s.2.1 = .rewrite ∧ ∃ e, HeadAt s.1 s.2.2 e (.contraction .term)))
    (first : Step s t) (second : Step s u) : Nonempty (StateIso t u) :=
  (step_coherent_or_copying first second).resolve_right outside

theorem cost_spectrum_away_copying {d I O} {s t : State d I O}
    (outside : ¬ (s.2.1 = .rewrite ∧ ∃ e, HeadAt s.1 s.2.2 e (.contraction .term)))
    (step : Step s t) (n : Nat) :
    TerminatesIn n s ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => step_deterministic_away_copying outside h step) n

theorem unbounded_coherent_or_copying {s t u : UnboundedState}
    (first : UnboundedStep s t) (second : UnboundedStep s u) :
    Represents t u ∨ (s.2.2.1 = .rewrite ∧ ∃ e, HeadAt s.2.1 s.2.2.2 e (.contraction .term)) := by
  cases first with
  | lift first => cases second with
    | lift second =>
      rcases step_coherent_or_copying first second with coherent | copying
      · obtain ⟨iso⟩ := coherent; exact .inl (.lift iso)
      · exact .inr copying
end Hypernets.Copying.Combined
