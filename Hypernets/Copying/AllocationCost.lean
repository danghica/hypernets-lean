import Hypernets.Copying.AllocationCoherence

/-! Exact-cost consequences of proved successor coherence. -/
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- A concrete search transition is the only combined transition from its source. -/
theorem search_successor_unique {d I O} {G : Hypernet d I O} {p q} {t : State d I O}
    (search : Search.Step G p q) (step : Step ⟨G,p⟩ t) : t = ⟨G,q⟩ := by
  cases step with
  | search _ step => exact congrArg (Sigma.mk G) (Search.deterministic step search)
  | rewrite _ => exact False.elim (Search.no_rewrite search)

/-- A final state has precisely the zero successful cost. -/
theorem final_cost_iff {d I O} {s : State d I O} (done : (machine d I O).final s) (n : Nat) :
    TerminatesIn n s ↔ n = 0 := by
  constructor
  · rintro ⟨t,run,_⟩
    exact (run.normal_eq (fun _ step => final_normal done _ step)).1
  · rintro rfl; exact ⟨s,.zero _,done⟩

/-- Local successor coherence suffices to remove one execution step at its exact cost. -/
theorem coherent_step_cost_iff {d I O} {s t : State d I O} (step : Step s t)
    (unique : ∀ u, Step s u → Nonempty (StateIso u t)) (n : Nat) :
    TerminatesIn n s ↔ ∃ m, n = m+1 ∧ TerminatesIn m t := by
  constructor
  · rintro ⟨u,run,done⟩
    cases run with
    | zero => exact False.elim (final_normal done _ step)
    | @cons m _ x _ first rest =>
      obtain ⟨iso⟩ := unique x first
      exact ⟨m,rfl,(terminatesIn_iso iso m).mp ⟨u,rest,done⟩⟩
  · rintro ⟨m,rfl,u,run,done⟩
    exact ⟨u,.cons step run,done⟩

/-- Exact successful-cost spectrum for an actual search transition. -/
theorem search_cost_iff {d I O} {G : Hypernet d I O} {p q} (step : Search.Step G p q) (n : Nat) :
    TerminatesIn n ⟨G,p⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m ⟨G,q⟩ :=
  coherent_step_cost_iff (.search G step)
    (fun _ h => ⟨StateIso.ofEq (search_successor_unique step h)⟩) n

/-- The zero-cost case is excluded as well: allocation has an exact one-step overhead. -/
theorem allocation_cost_spectrum {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation (.unary .ref)))
    (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn n ⟨G,(.rewrite,v)⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => allocation_step_deterministic head h step) n
end Hypernets.Copying.Combined
