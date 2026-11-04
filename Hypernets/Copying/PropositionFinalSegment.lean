import Hypernets.Copying.PropositionParametricityInstance

/-! The completed last two links of Figure 22 in every finite environment
and at every adequate common allowance. The separate original-left-to-
parametricity normalization is deliberately not a premise of these theorems. -/
namespace Hypernets.Copying.Proposition12_2.ParametricInstance
open Graph

def privateEnvironment (d k h : Nat) : OpenProgram (d+2) k h :=
  Weakening.ambientProgram (privateProgram d) k h

/-- Compose concrete parametricity with normalization back to the unchanged
right-hand term, transporting through the actual sole-hole ambient context. -/
theorem private_original_environment (d k h : Nat) : Combined.execution.Equiv CostOrder.any
    (privateEnvironment d k h) (Result.originalEnvironment d k h) := by
  have param := Weakening.ambient_equiv _ _ (equivalent d) k h
  have normalization := Result.original_normalized_environment d k h
  exact Combined.execution.equiv_trans param ⟨normalization.2,normalization.1⟩

theorem private_original_named {Name : Type} (E : Environment Name) (d : Nat) :
    Combined.execution.Equiv CostOrder.any
      (privateEnvironment d E.variables.length E.atoms.length)
      (Result.originalEnvironment d E.variables.length E.atoms.length) :=
  private_original_environment _ _ _

/-- The full final segment applies at any specified adequate common depth,
with the exact translatedProgram endpoint used by ObservationalEquiv. -/
theorem private_original_at {N k h : Nat} (bound : 2 ≤ N) :
    ∃ d, ∃ eq : d+2 = N,
      Combined.execution.Equiv CostOrder.any
        (privateEnvironment d k h)
        (translatedProgram (Term.constantResult k h) (d+2) (by change 2 ≤ d+2; omega)) := by
  refine ⟨N-2,by omega,?_⟩
  exact private_original_environment _ _ _

/-- Equality of successful termination is quantified over the full original
binding-free observation class, not only translated term contexts. -/
theorem private_original_termination {d k h} (C : ClosingContext (d+2) k h) :
    Combined.execution.Terminates (C.close (privateEnvironment d k h)) ↔
      Combined.execution.Terminates (C.close (Result.originalEnvironment d k h)) :=
  (Combined.execution.equiv_any_iff _ _).mp (private_original_environment d k h) C

/-- The reverse quantitative bound is retained for the closed final segment. -/
theorem private_original_reverse_overhead (d : Nat) : Combined.execution.Refines CostOrder.overhead
    (Result.originalAt d) (privateProgram d) := by
  intro C
  exact (((Result.original_normalizedAt_exact d).1 C).mono
    (by intro a b eq; cases eq; exact Nat.le_refl _)).trans (reverse_overhead d C)

/-- The allocating program requires allowance three. This specialization
already ends at its literal right-hand comparison program in mixed environments. -/
theorem common_depth_three (k h : Nat) : Combined.execution.Equiv CostOrder.any
    (privateEnvironment 1 k h) (translatedProgram (Term.constantResult k h) 3 (by change 2 ≤ 3; decide)) :=
  private_original_environment 1 k h

/-- Retaining a noncanonical private sharing tree requires no extra
normalization premise at the final equivalence segment. -/
def privateProgramWith (d : Nat) (C : ContractionTree .term 1) : OpenProgram (d+2) 0 0 :=
  ⟨privateClosureWith d C,(pairWith d C).closed.1.1,(pairWith d C).closed.1.2⟩

theorem private_original_with_tree (d : Nat) (C : ContractionTree .term 1) (k h : Nat) :
    Combined.execution.Equiv CostOrder.any
      (Weakening.ambientProgram (privateProgramWith d C) k h)
      (Result.originalEnvironment d k h) := by
  have eq : Combined.execution.Equiv CostOrder.any (privateProgramWith d C) (Result.normalizedAt d) :=
    Parametricity.pair_contextual_equiv _ _ (pairWith d C)
  have lifted := Weakening.ambient_equiv _ _ eq k h
  have right := Result.original_normalized_environment d k h
  exact Combined.execution.equiv_trans lifted ⟨right.2,right.1⟩

end Hypernets.Copying.Proposition12_2.ParametricInstance
