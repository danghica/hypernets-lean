import Hypernets.LocalReasoning

/-!
Small semantic regression proofs: quantitative direction, the stuck branch,
and the zero-step case in the converse robustness argument. These are abstract
machines, not claims about the paper's lambda-calculus examples.
-/

namespace Hypernets.Examples

def countdown : Machine Nat where
  step s t := s = t + 1
  final s := s = 0
  final_normal := by intros; omega

theorem countdown_deterministic : countdown.Deterministic := by
  intro s a b ha hb
  dsimp [countdown] at *
  omega

theorem countdown_run (n : Nat) : countdown.Steps n n 0 := by
  induction n with
  | zero => exact .zero _
  | succ n ih => exact .cons rfl ih

/-- The cost relation really compares the source length to the target length. -/
theorem countdown_refines_iff (Q : CostOrder) (a b : Nat) :
    countdown.Refines Q a b ↔ Q.rel a b := by
  constructor
  · intro h
    obtain ⟨m, z, cost, path, hz⟩ := h (countdown_run a) rfl
    have eq := path.final_unique countdown_deterministic (countdown_run b) hz rfl
    exact eq.1 ▸ cost
  · intro cost n z path hz
    have eq := path.final_unique countdown_deterministic (countdown_run a) hz rfl
    exact ⟨b, 0, eq.1.symm ▸ cost, countdown_run b, rfl⟩

example : countdown.Refines CostOrder.improvement 5 3 :=
  (countdown_refines_iff _ _ _).mpr (by change 3 ≤ 5; decide)

example : ¬ countdown.Refines CostOrder.improvement 3 5 := by
  rw [countdown_refines_iff]
  change ¬ 5 ≤ 3
  decide

example : ¬ countdown.Refines CostOrder.exact 5 3 := by
  rw [countdown_refines_iff]
  change ¬ (5 : Nat) = 3
  decide

inductive FaultState where
  | done | crash | stuck | loop
  deriving DecidableEq

def fault : Machine FaultState where
  step s t := (s = .crash ∧ t = .stuck) ∨ (s = .loop ∧ t = .loop)
  final s := s = .done
  final_normal := by
    intro s t hs st
    rcases st with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all

theorem fault_deterministic : fault.Deterministic := by
  intro s a b ha hb
  rcases ha with ⟨sa, ha⟩ | ⟨sa, ha⟩ <;>
    rcases hb with ⟨sb, hb⟩ | ⟨sb, hb⟩ <;> simp_all

def crashLoop (s t : FaultState) : Prop := s = .crash ∧ t = .loop

/-- The stuck alternative of simulation is necessary: the left computation
crashes while the right computation loops forever. Neither successfully ends. -/
theorem crash_loop_simulation :
    fault.CountingSimulation CostOrder.exact CostOrder.exact CostOrder.exact crashLoop where
  final_match := by
    rintro s t ⟨rfl, rfl⟩ h
    cases h
  progress := by
    rintro s t s' ⟨rfl, rfl⟩ step
    have eq : s' = .stuck := by
      rcases step with ⟨_, eq⟩ | ⟨bad, _⟩
      · exact eq
      · cases bad
    subst s'
    left
    refine ⟨0, .stuck, .zero _, ?_, ?_⟩
    · intro t step
      rcases step with ⟨bad, _⟩ | ⟨bad, _⟩ <;> cases bad
    · intro bad
      cases bad

example : fault.Refines CostOrder.exact .crash .loop :=
  crash_loop_simulation.sound fault_deterministic CostOrder.reasonable_exact ⟨rfl, rfl⟩

inductive Visit where
  | entering | settled | finished
  deriving DecidableEq

def visitLeft : Visit → Nat
  | .entering => 2
  | .settled => 1
  | .finished => 0

def visitRight : Visit → Nat
  | .entering => 1
  | .settled => 1
  | .finished => 0

def visitSystem : SpecimenSystem countdown where
  Specimen := Visit
  left := visitLeft
  right := visitRight
  mode _ := .search
  entering c := c = .entering
  rooted _ := True
  rooted_step := by intros; trivial
  same_final := by intro c; cases c <;> simp [countdown, visitLeft, visitRight]
  context_step := by
    intro c _ _ settled available
    cases c with
    | entering =>
        rcases settled with bad | ⟨_, bad⟩
        · cases bad
        · exact False.elim (bad rfl)
    | settled => exact ⟨.finished, Or.inl (by decide), rfl, rfl⟩
    | finished =>
        rcases available with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
          simp [countdown, visitLeft, visitRight] at hs

/-- Safety II uses one left step and *zero* right steps. -/
theorem visit_safe : visitSystem.InputSafe CostOrder.overhead.converse CostOrder.exact := by
  intro c _ _ _ entering
  have eq : c = .entering := entering
  subst c
  right; left
  exact ⟨.settled, 0, 0,
    Or.inr ⟨rfl, by change Visit.settled ≠ Visit.entering; decide⟩,
    by change 0 ≤ 1; decide,
    .cons rfl (.zero _), .zero _⟩

theorem visit_converse_robust :
    visitSystem.opposite.Robust CostOrder.overhead CostOrder.exact CostOrder.exact := by
  intro c _ _ bad
  cases bad

/-- Exercises the extra traversal in reverse safety II when the right path
has length zero, rather than merely checking an identity relation. -/
theorem converse_zero_step_case : countdown.Refines CostOrder.overhead 1 2 :=
  visitSystem.sufficiency_converse countdown_deterministic CostOrder.reasonable_overhead
    visit_safe visit_converse_robust
    ⟨.entering, Or.inl (by decide), trivial, trivial, rfl, rfl⟩

end Hypernets.Examples
