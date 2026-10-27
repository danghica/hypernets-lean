import Hypernets.Copying.CopyCost

/-! Full-machine regressions for the original copying rule and finite-depth padding. -/
namespace Hypernets.Copying.CopyRule.Examples
open Graph Combined

/-- A closed copying redex using the existing one-input contraction tree. -/
def constantProgram (c : Constant) : ClosedProgram where
  depth := 0
  graph := before (k := 0) (h := 0) (ContractionTree.canonical .term 1) (primitiveNet 0 (.operation (.const c)))
  focusFree := before_allLabels _ _ _ (Stable.focusFree (.constant 0 c))
    (by intro m h; cases h) (by intro m h; cases h)
  holeFree := before_allLabels _ _ _ (Stable.holeFree (.constant 0 c))
    (by intro m h; cases h) (by intro m h; cases h)

/-- All successful runs of this unbounded closed program, at every padding, cost three. -/
theorem constant_pad_cost_iff (c : Constant) (layers cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial ((constantProgram c).pad layers)) t ∧
      unboundedMachine.final t) ↔ cost = 3 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  exact constant_cost_iff _ 0 c cost

/-- Copying the literal translated nested-lambda body returns without running either body. -/
theorem nested_lambda_cost_iff (cost : Nat) :
    TerminatesIn cost ⟨before (ContractionTree.canonical .term 1)
      (lambdaPayload Application.Examples.nestedBody),(.search,.input ⟨0,by simp⟩)⟩ ↔ cost = 3 :=
  lambda_cost_iff _ _ cost

/-- Two repeated reference uses preserve one uniquely resolved store after copying. -/
theorem shared_reference_unique {n} (T : ContractionTree .term (n+1))
    {leftCell rightCell : (sharedStore T).Edge} {leftCost rightCost}
    (left : StoreTrace.Resolves (sharedStore T) (sharedLeft T) leftCell leftCost)
    (right : StoreTrace.Resolves (sharedStore T) (sharedRight T) rightCell rightCost) :
    leftCell = rightCell ∧ leftCost = 3 ∧ rightCost = 3 := by
  have l := StoreTrace.resolves_unique left (shared_resolves T).1
  have r := StoreTrace.resolves_unique right (shared_resolves T).2
  exact ⟨l.1.trans r.1.symm,l.2,r.2⟩
end Hypernets.Copying.CopyRule.Examples
