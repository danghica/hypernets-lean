import Hypernets.Copying.ArithmeticCoherence

/-! The two remaining families in full-machine successor coherence are explicit.
This is a theorem about the original transition relation, not a restricted machine. -/
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- The only heads whose whole-successor coherence remains to be proved. -/
inductive HigherOrderHead {d I O} (G : Hypernet d I O) (v : G.Vertex) : Prop where
  | application {e} : HeadAt G v e (.operation .app) → HigherOrderHead G v
  | copying {e} : HeadAt G v e (.contraction .term) → HigherOrderHead G v

/-- Any pair of actual rewrites is coherent or has an application/copying head. -/
theorem rewrite_coherent_or_higherOrder {d I O} {G H K : Hypernet d I O} {v w u}
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) ∨ HigherOrderHead G v := by
  obtain ⟨choice,recognized⟩ := rewrite_recognizes first
  have witness := recognized
  obtain ⟨e,head,_⟩ := witness
  cases choice with
  | allocate => exact .inl (allocation_rewrite_deterministic head first second)
  | read => exact .inl (dereference_rewrite_deterministic head first second)
  | assign => exact .inl (assignment_rewrite_deterministic head first second)
  | compare _ => exact .inl (equality_rewrite_deterministic head first second)
  | beta => exact .inr (.application head)
  | copy _ => exact .inr (.copying head)
  | neg n => exact .inl (arithmetic_rewrite_deterministic (.neg n) recognized first second)
  | binary o m n => exact .inl (arithmetic_rewrite_deterministic (.binary o m n) recognized first second)

/-- A full-machine pair of successors can fail coherence only at a rewrite request
for application or copying. Search and every store/arithmetic operation are covered. -/
theorem step_coherent_or_higherOrder {d I O} {s t u : State d I O}
    (first : Step s t) (second : Step s u) :
    Nonempty (StateIso t u) ∨ (s.2.1 = .rewrite ∧ HigherOrderHead s.1 s.2.2) := by
  cases first with
  | search G h => exact .inl ⟨StateIso.ofEq (search_successor_unique h second).symm⟩
  | rewrite first =>
    cases second with
    | search G h => exact False.elim (Search.no_rewrite h)
    | rewrite second =>
      rcases rewrite_coherent_or_higherOrder first second with coherent | higher
      · exact .inl coherent
      · exact .inr ⟨rfl,higher⟩

/-- Whole-successor determinism is now unconditional away from the two remaining heads. -/
theorem step_deterministic_away_higherOrder {d I O} {s t u : State d I O}
    (outside : ¬ (s.2.1 = .rewrite ∧ HigherOrderHead s.1 s.2.2))
    (first : Step s t) (second : Step s u) : Nonempty (StateIso t u) :=
  (step_coherent_or_higherOrder first second).resolve_right outside

/-- Every completed family has an exact one-step successful-cost decomposition. -/
theorem cost_spectrum_away_higherOrder {d I O} {s t : State d I O}
    (outside : ¬ (s.2.1 = .rewrite ∧ HigherOrderHead s.1 s.2.2))
    (step : Step s t) (n : Nat) :
    TerminatesIn n s ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => step_deterministic_away_higherOrder outside h step) n

/-- The same exhaustive classification applies to the unbounded copying machine. -/
theorem unbounded_coherent_or_higherOrder {s t u : UnboundedState}
    (first : UnboundedStep s t) (second : UnboundedStep s u) :
    Represents t u ∨ (s.2.2.1 = .rewrite ∧ HigherOrderHead s.2.1 s.2.2.2) := by
  cases first with
  | lift first =>
    cases second with
    | lift second =>
      rcases step_coherent_or_higherOrder first second with coherent | higher
      · obtain ⟨iso⟩ := coherent
        exact .inl (.lift iso)
      · exact .inr higher
end Hypernets.Copying.Combined
