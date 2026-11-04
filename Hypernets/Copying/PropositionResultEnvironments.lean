import Hypernets.Copying.PropositionResultPadding

/-! The unchanged right program in every finite environment and at every
adequate common depth, connected to the normalized Figure 20 abstraction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2.Result
open Graph Weakening

/-- Actual ambient weakenings commute with finite representation padding. -/
theorem ambient_padTo {d} (G : Hypernet d [.term] []) (k h N : Nat) (bound : d ≤ N) :
    Translation.padTo N bound (ambient G k h) = ambient (Translation.padTo N bound G) k h := by
  have vars : ∀ k, Translation.padTo N bound (addVariables (h := 0) G k) =
      addVariables (h := 0) (Translation.padTo N bound G) k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => change Translation.padTo N bound (BoxPullWeakening.extend _ .term) = _
                   rw [extend_padTo,ih]; rfl
  induction h with
  | zero => exact vars k
  | succ h ih => change Translation.padTo N bound (BoxPullWeakening.extend _ .atom) = _
                 rw [extend_padTo]
                 exact congrArg (fun X => BoxPullWeakening.extend X .atom) ih

def originalEnvironment (d k h : Nat) : OpenProgram (d+2) k h :=
  translatedProgram (Term.constantResult k h) (d+2) (by change 2 ≤ d+2; omega)
def normalizedEnvironment (d k h : Nat) : OpenProgram (d+2) k h :=
  ambientProgram (normalizedAt d) k h

/-- Exact syntactic weakening of the original translation survives the chosen
common allowance and reconstructs the certified outside-weakening context. -/
theorem environment_weakening_exact (d k h : Nat) :
    Combined.execution.Equiv CostOrder.exact (originalEnvironment d k h)
      (ambientProgram (originalAt d) k h) := by
  have c := (constantResult_environment k h).padTo (d+2) (by change 2 ≤ d+2; omega)
  rw [ambient_padTo] at c
  exact c.contextual_exact

/-- Full right-hand normalization, with the original term, all finite free
environments, all depth allowances and every binding-free closing context. -/
theorem original_normalized_environment (d k h : Nat) :
    Combined.execution.Equiv CostOrder.any (originalEnvironment d k h) (normalizedEnvironment d k h) := by
  have first : Combined.execution.Equiv CostOrder.any (originalEnvironment d k h)
      (ambientProgram (originalAt d) k h) :=
    ⟨fun C => ((environment_weakening_exact d k h).1 C).mono (fun _ => trivial),
      fun C => ((environment_weakening_exact d k h).2 C).mono (fun _ => trivial)⟩
  exact Combined.execution.equiv_trans first
    (ambient_equiv _ _ (original_normalizedAt d) k h)

theorem original_normalized_named {Name : Type} (E : Environment Name) (d : Nat) :
    Combined.execution.Equiv CostOrder.any
      (originalEnvironment d E.variables.length E.atoms.length)
      (normalizedEnvironment d E.variables.length E.atoms.length) :=
  original_normalized_environment _ _ _

/-- This observation includes arbitrary repeated use, divergence and stuckness
of callbacks: neither successful termination nor single use is assumed. -/
theorem original_normalized_termination {d k h} (C : ClosingContext (d+2) k h) :
    Combined.execution.Terminates (C.close (originalEnvironment d k h)) ↔
      Combined.execution.Terminates (C.close (normalizedEnvironment d k h)) :=
  (Combined.execution.equiv_any_iff _ _).mp (original_normalized_environment d k h) C
end Hypernets.Copying.Proposition12_2.Result
