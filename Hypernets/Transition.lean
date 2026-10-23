import Std

/-!
Finite executions of an abstract machine. This module isolates the deterministic
rewriting facts used in Appendix F of arXiv:1907.01257v5.
-/

namespace Hypernets

universe u

structure Machine (State : Type u) where
  step : State → State → Prop
  final : State → Prop
  final_normal : ∀ {s t}, final s → ¬ step s t

namespace Machine

variable {State : Type u} (M : Machine State)

def Deterministic : Prop :=
  ∀ ⦃s t₁ t₂⦄, M.step s t₁ → M.step s t₂ → t₁ = t₂

def Normal (s : State) : Prop := ∀ t, ¬ M.step s t

/-- A stuck state is a normal form which is not a successful final state. -/
def Stuck (s : State) : Prop := M.Normal s ∧ ¬ M.final s

/-- Exactly `n` transitions, including all search and rewrite transitions. -/
inductive Steps : Nat → State → State → Prop where
  | zero (s) : Steps 0 s s
  | cons {n s t v} : M.step s t → Steps n t v → Steps (n + 1) s v

variable {M}

theorem Steps.zero_eq {s t : State} (h : M.Steps 0 s t) : s = t := by
  cases h
  rfl

theorem Steps.append {m n : Nat} {s t v : State}
    (h : M.Steps m s t) (h' : M.Steps n t v) : M.Steps (m + n) s v := by
  induction h with
  | zero => simpa using h'
  | cons st _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons st (ih h')

theorem Steps.normal_eq {n : Nat} {s t : State}
    (h : M.Steps n s t) (normal : M.Normal s) : n = 0 ∧ s = t := by
  cases h with
  | zero => exact ⟨rfl, rfl⟩
  | cons st _ => exact False.elim (normal _ st)

/-- Every execution from a terminating state is a prefix of its terminating run. -/
theorem Steps.prefix_of_final (det : M.Deterministic)
    {m n : Nat} {s t z : State} (path : M.Steps m s t)
    (run : M.Steps n s z) (hz : M.final z) :
    ∃ r, n = m + r ∧ M.Steps r t z := by
  induction path generalizing n with
  | zero => exact ⟨n, by omega, run⟩
  | @cons m s t v st tv ih =>
      cases run with
      | zero => exact False.elim (M.final_normal hz st)
      | cons st' tz =>
          have e := det st st'
          subst e
          obtain ⟨r, count, tail⟩ := ih tz
          exact ⟨r, by omega, tail⟩

theorem Steps.final_unique (det : M.Deterministic)
    {m n : Nat} {s t z : State} (h : M.Steps m s t) (h' : M.Steps n s z)
    (ht : M.final t) (hz : M.final z) : m = n ∧ t = z := by
  obtain ⟨r, count, tail⟩ := h.prefix_of_final det h' hz
  obtain ⟨hr, eq⟩ := tail.normal_eq (fun _ st => M.final_normal ht st)
  exact ⟨by omega, eq⟩

theorem Steps.not_stuck_of_final (det : M.Deterministic)
    {m n : Nat} {s t z : State} (h : M.Steps m s t) (h' : M.Steps n s z)
    (hz : M.final z) : ¬ M.Stuck t := by
  intro ht
  obtain ⟨r, _, tail⟩ := h.prefix_of_final det h' hz
  obtain ⟨_, eq⟩ := tail.normal_eq ht.1
  exact ht.2 (eq.symm ▸ hz)

theorem Steps.drop_first (det : M.Deterministic)
    {n : Nat} {s s' t : State} (st : M.step s s')
    (run : M.Steps (n + 1) s t) : M.Steps n s' t := by
  cases run with
  | cons first tail =>
      have eq := det st first
      exact eq.symm ▸ tail

/-- A run ending in a stuck state cannot have length zero if a step is available. -/
theorem Steps.stuck_after_step (det : M.Deterministic)
    {n : Nat} {s s' t : State} (st : M.step s s')
    (run : M.Steps n s t) (ht : M.Stuck t) :
    ∃ k, M.Steps k s' t := by
  cases run with
  | zero => exact False.elim (ht.1 _ st)
  | cons first tail =>
      have eq := det st first
      exact ⟨_, eq.symm ▸ tail⟩

end Machine
end Hypernets
