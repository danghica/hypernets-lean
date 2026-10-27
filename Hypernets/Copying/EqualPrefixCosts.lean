import Hypernets.Copying.BoxPermutationCopying

/-! Cancellation of equal finite prefixes in the concrete machine, including
arbitrary typed plugging contexts. All costs count original machine transitions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- Reindex a state along equal input and output lists. This changes no graph
or transition; it only supplies the interface types demanded by a host slot. -/
def castInterfaces {d I O J K} (hi : I = J) (ho : O = K) (s : State d I O) : State d J K := by
  cases hi; cases ho; exact s

theorem run_castInterfaces {d I O J K} (hi : I = J) (ho : O = K)
    {s t : State d I O} {n} (run : (machine d I O).Steps n s t) :
    (machine d J K).Steps n (castInterfaces hi ho s) (castInterfaces hi ho t) := by
  cases hi; cases ho; exact run

def StateIso.castInterfaces {d I O J K} (hi : I = J) (ho : O = K)
    {s t : State d I O} (iso : StateIso s t) :
    StateIso (Combined.castInterfaces hi ho s) (Combined.castInterfaces hi ho t) := by
  cases hi; cases ho; exact iso

/-- Two equal-length actual prefixes leading to isomorphic states imply exact
cost equivalence of their sources, using proved successor coherence. -/
theorem equal_prefix_costs {d I O} {s t u v : State d I O} {n}
    (left : (machine d I O).Steps n s u) (right : (machine d I O).Steps n t v)
    (iso : StateIso u v) (cost : Nat) : TerminatesIn cost s ↔ TerminatesIn cost t := by
  rw [run_cost_spectrum left,run_cost_spectrum right]
  exact exists_congr (fun rest => and_congr Iff.rfl (terminatesIn_iso iso rest))

/-- The same cancellation holds in every typed slot. Local termination is never
identified with global termination: both prefixes and the endpoint isomorphism
are lifted first, and cost cancellation is then applied to the whole machine. -/
theorem equal_prefix_costs_plug {d I O} (C : Hypernet d I O) (e : C.Edge)
    {s t u v : State d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {n}
    (left : (machine d _ _).Steps n s u) (right : (machine d _ _).Steps n t v)
    (iso : StateIso u v) (cost : Nat) :
    TerminatesIn cost (plugState C e s) ↔ TerminatesIn cost (plugState C e t) :=
  equal_prefix_costs (run_plug C e left) (run_plug C e right) (iso.plug C e) cost

/-- Cancelling two equal prefixes is also an equivalence at the level of the
whole successful cost spectrum; the backwards implication adds the common cost. -/
theorem equal_prefix_spectra_iff {d I O} {s t u v : State d I O} {n}
    (left : (machine d I O).Steps n s u) (right : (machine d I O).Steps n t v) :
    (∀ cost, TerminatesIn cost s ↔ TerminatesIn cost t) ↔
      (∀ rest, TerminatesIn rest u ↔ TerminatesIn rest v) := by
  constructor
  · intro eq rest
    have h := eq (rest+n)
    rw [run_cost_spectrum left,run_cost_spectrum right] at h
    simpa using h
  · intro eq cost
    rw [run_cost_spectrum left,run_cost_spectrum right]
    exact exists_congr (fun rest => and_congr Iff.rfl (eq rest))
/-- Apply a local equal-prefix comparison in any host with the matching ordered
interfaces, making all dependent-type casts explicit. -/
theorem equal_prefix_costs_at {d I O J K} (C : Hypernet d I O) (e : C.Edge)
    (hi : J = (alphabet d).signature.input (C.edgeLabel e))
    (ho : K = (alphabet d).signature.output (C.edgeLabel e))
    {s t u v : State d J K} {n}
    (left : (machine d J K).Steps n s u) (right : (machine d J K).Steps n t v)
    (iso : StateIso u v) (cost : Nat) :
    TerminatesIn cost (plugState C e (castInterfaces hi ho s)) ↔
      TerminatesIn cost (plugState C e (castInterfaces hi ho t)) :=
  equal_prefix_costs_plug C e (run_castInterfaces hi ho left) (run_castInterfaces hi ho right)
    (iso.castInterfaces hi ho) cost

/-- Exact cancellation in a host also works when endpoints are related by a
remaining template obligation rather than already being isomorphic. -/
theorem equal_prefix_spectra_at {d I O J K} (C : Hypernet d I O) (e : C.Edge)
    (hi : J = (alphabet d).signature.input (C.edgeLabel e))
    (ho : K = (alphabet d).signature.output (C.edgeLabel e))
    {s t u v : State d J K} {n}
    (left : (machine d J K).Steps n s u) (right : (machine d J K).Steps n t v) :
    (∀ cost, TerminatesIn cost (plugState C e (castInterfaces hi ho s)) ↔
      TerminatesIn cost (plugState C e (castInterfaces hi ho t))) ↔
    (∀ rest, TerminatesIn rest (plugState C e (castInterfaces hi ho u)) ↔
      TerminatesIn rest (plugState C e (castInterfaces hi ho v))) :=
  equal_prefix_spectra_iff (run_plug C e (run_castInterfaces hi ho left))
    (run_plug C e (run_castInterfaces hi ho right))
end Hypernets.Copying.Combined
