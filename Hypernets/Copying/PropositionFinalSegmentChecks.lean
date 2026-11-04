import Hypernets.Copying.PropositionFinalSegment

/-! Concrete structural and semantic regression cases for the last two
Figure 22 links. They retain the callback computation and cover original
allowances, mixed environments, and noncanonical private sharing. -/
namespace Hypernets.Copying.Proposition12_2.FinalSegmentChecks
open Graph

/-- Structural simplification removes sharing edges, not application heads. -/
def applications (G : Hypernet 1 [.term] [.term]) : Nat :=
  G.finiteEdge.elements.countP fun e => match G.edgeLabel e with
    | .inl (.operation .app) => true
    | _ => false

theorem callback_computation_retained :
    applications (Translation.term Result.bodyTerm) = 2 ∧
    applications Result.mixed = 2 ∧ applications (Parametricity.callOneBody 0) = 2 := by decide

/-- This cannot be a mere graph isomorphism: the checked steps genuinely
remove unused sharing while retaining the original operational skeleton. -/
theorem sharing_edge_inventory :
    (Translation.term Result.bodyTerm).finiteEdge.elements.length = 16 ∧
    Result.mixed.finiteEdge.elements.length = 15 ∧
    Result.sharing.finiteEdge.elements.length = 10 ∧
    (Parametricity.callOneBody 0).finiteEdge.elements.length = 7 := by decide

/-- Canonical private-cell elimination removes the actual store component,
whereas the earlier allocation/beta milestone deliberately retained it. -/
theorem private_edge_inventory :
    (ParametricInstance.privateClosure 1).finiteEdge.elements.length = 9 ∧
    (Parametricity.largeRight 1).finiteEdge.elements.length = 2 := by decide

/-- The ten-edge tree extracted from the literal translation may itself be
retained as the private sharing tree; no canonical-tree premise is needed. -/
theorem noncanonical_mixed_environment : Combined.execution.Equiv CostOrder.any
    (Weakening.ambientProgram (ParametricInstance.privateProgramWith 1 Result.sharing_tree.tree) 2 3)
    (translatedProgram (Term.constantResult 2 3) 3 (by decide)) :=
  ParametricInstance.private_original_with_tree 1 Result.sharing_tree.tree 2 3

/-- Exact successful counts agree for the original right program under any
binding-free observation, including repeated or divergent callback use. -/
theorem exact_observation_count {d} (C : ClosingContext (d+2) 0 0) (n : Nat) :
    (∃ a, Combined.unboundedMachine.Steps n
      (Combined.execution.initial (C.close (Result.originalAt d))) a ∧ Combined.unboundedMachine.final a) ↔
    (∃ b, Combined.unboundedMachine.Steps n
      (Combined.execution.initial (C.close (Result.normalizedAt d))) b ∧ Combined.unboundedMachine.final b) := by
  have eq := Result.original_normalizedAt_exact d
  constructor
  · rintro ⟨a,run,done⟩
    obtain ⟨m,b,cost,run',done'⟩ := eq.1 C run done
    cases cost
    exact ⟨b,run',done'⟩
  · rintro ⟨b,run,done⟩
    obtain ⟨m,a,cost,run',done'⟩ := eq.2 C run done
    cases cost
    exact ⟨a,run',done'⟩
end Hypernets.Copying.Proposition12_2.FinalSegmentChecks
