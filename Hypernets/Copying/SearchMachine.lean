import Hypernets.Copying.SearchLocality

/-! The concrete search-phase machine and exact cost-preserving run transport.
A rewrite focus is a suspension for the future copying/compute phase, not a
claim that the full copying UAM is stuck. No Execution instance is supplied. -/
namespace Hypernets.Copying.Search
open Graph

/-- A value has returned to an external input. -/
def Completed {d I O} {G : Hypernet d I O} (s : Position G) : Prop :=
  s.1 = .backtrack ∧ s.2.IsInput

/-- The phase machine contains exactly the proved intrinsic search interactions. -/
def machine {d I O} (G : Hypernet d I O) : Machine (Position G) where
  step := Step G
  final := Completed
  final_normal := by
    rintro ⟨m,v⟩ t ⟨eq,input⟩
    change m = .backtrack at eq
    subst m
    exact final_no_step input

theorem machine_deterministic {d I O} (G : Hypernet d I O) : (machine G).Deterministic :=
  fun _ _ _ a b => deterministic a b

/-- The generic machine counter and finite relation traces count exactly the same steps. -/
theorem steps_iff_trace {d I O} (G : Hypernet d I O) (n : Nat) (s t : Position G) :
    (machine G).Steps n s t ↔ Trace (Step G) s t n := by
  constructor
  · intro run
    induction run with
    | zero => exact .refl _
    | cons h _ ih => exact .step h ih
  · intro run
    induction run with
    | refl => exact .zero _
    | step h _ ih => exact .cons h ih

namespace Transport
variable {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}

theorem completed_iff (f : Transport G H) (s : Position G) : Completed (f.positions.toFun s) ↔ Completed s :=
  and_congr Iff.rfl (f.input_iff s.2)

theorem machine_steps_iff (f : Transport G H) (n : Nat) (s t : Position G) :
    (machine H).Steps n (f.positions.toFun s) (f.positions.toFun t) ↔ (machine G).Steps n s t :=
  (steps_iff_trace H n _ _).trans ((f.trace_iff s t n).trans (steps_iff_trace G n s t).symm)

/-- Successful phase runs correspond at exactly the same cost, in both directions. -/
theorem completes_at_iff (f : Transport G H) (s : Position G) (n : Nat) :
    (∃ t, (machine H).Steps n (f.positions.toFun s) t ∧ Completed t) ↔
      (∃ t, (machine G).Steps n s t ∧ Completed t) := by
  constructor
  · rintro ⟨t,run,done⟩
    refine ⟨f.positions.invFun t,?_,?_⟩
    · apply (f.machine_steps_iff n s _).mp
      simpa [f.positions.right_inv] using run
    · apply (f.completed_iff _).mp
      simpa [f.positions.right_inv] using done
  · rintro ⟨t,run,done⟩
    exact ⟨f.positions.toFun t,(f.machine_steps_iff n s t).mpr run,(f.completed_iff t).mpr done⟩
end Transport

/-- Exact phase costs, not just possible termination, survive any common allowance. -/
theorem padding_completion_iff {d I O} (G : Hypernet d I O) (N : Nat) (bound : d ≤ N)
    (s : Position G) (n : Nat) :
    (∃ t, (machine (Translation.padTo N bound G)).Steps n ((padTo G N bound).positions.toFun s) t ∧ Completed t) ↔
      (∃ t, (machine G).Steps n s t ∧ Completed t) :=
  (padTo G N bound).completes_at_iff s n
end Hypernets.Copying.Search
