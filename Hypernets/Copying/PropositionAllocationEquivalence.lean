import Hypernets.Copying.PropositionAllocationPrograms

/-! The original allocating term reaches its opened-body/store intermediate
by proved operational templates in actual binding-free graph contexts. -/
namespace Hypernets.Copying.Proposition12_2
open Graph

theorem referencePair : OperationalTemplates.Pair .referenceCreation referenceSource.graph referenceTarget.graph :=
  .witness (DeepIso.refl _) (.reference _ (Stable.constant 3 (.nat 1))) (DeepIso.refl _)

theorem betaPair : OperationalTemplates.Pair .microBeta betaLeft.graph betaRight.graph :=
  .witness (DeepIso.refl _) (.beta body _ body_focusFree (Stable.instanceEdge 3)) (DeepIso.refl _)

/-- Directed quantitative comparisons are retained before forgetting costs. -/
theorem reference_improvement : Combined.execution.Refines CostOrder.improvement referenceSource referenceTarget :=
  OperationalTemplates.pair_contextual_improvement _ _ referencePair

theorem beta_improvement : Combined.execution.Refines CostOrder.improvement betaLeft betaRight :=
  OperationalTemplates.pair_contextual_improvement _ _ betaPair

/-- Allocation in the actual left program, including its original lambda body. -/
theorem original_allocated : Combined.execution.Equiv CostOrder.any originalProgram allocatedProgram :=
  context_equiv (applicationContext (Application.closure body) closure_focusFree closure_holeFree)
    referenceSource referenceTarget originalProgram allocatedProgram
    (OperationalTemplates.pair_contextual_equiv _ _ referencePair)
    ((applicationContext_fill _ _ _ _).trans source_iso.symm)
    (applicationContext_fill _ _ _ _)

/-- The store factorization is a representation isomorphism, with no compute step. -/
theorem allocated_betaSource : Combined.execution.Equiv CostOrder.any allocatedProgram betaSourceProgram :=
  Combined.execution.equiv_iso Combined.execution_respectsIso _ _ allocated_iso

/-- Micro-beta opens the original outer body; its allocated store remains in
an explicitly certified binding-free suffix context. -/
theorem betaSource_opened : Combined.execution.Equiv CostOrder.any betaSourceProgram openedProgram :=
  context_equiv (storeContext (storeSuffix 3) (storeSuffix_focusFree 3) (storeSuffix_holeFree 3))
    betaLeft betaRight betaSourceProgram openedProgram
    (OperationalTemplates.pair_contextual_equiv _ _ betaPair)
    (storeContext_fill _ _ _ _) (storeContext_fill _ _ _ _)

/-- A concrete contextual equivalence from the unmodified translated left
program to its actual allocated and beta-opened intermediate graph. -/
theorem original_opened : Combined.execution.Equiv CostOrder.any originalProgram openedProgram :=
  Combined.execution.equiv_trans original_allocated
    (Combined.execution.equiv_trans allocated_betaSource betaSource_opened)

theorem original_opened_termination (C : ClosingContext 3 0 0) :
    Combined.execution.Terminates (C.close originalProgram) ↔
      Combined.execution.Terminates (C.close openedProgram) :=
  (Combined.execution.equiv_any_iff _ _).mp original_opened C
end Hypernets.Copying.Proposition12_2
