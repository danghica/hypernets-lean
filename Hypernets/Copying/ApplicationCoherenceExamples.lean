import Hypernets.Copying.ApplicationCost

/-! Full-machine all-run regressions using the unchanged Figure 16 body translations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.Examples
open Graph Combined

/-- An unused-parameter literal has exactly seven successful transitions in the full machine. -/
theorem constant_cost_iff {O} (c : Constant) (G : Hypernet 1 [.term] O) (stable : Stable G) (cost : Nat) :
    TerminatesIn cost ⟨before (constantBody c) G,(.search,.input 0)⟩ ↔ cost = 7 := by
  rw [opening_cost_iff _ _ stable]
  simp only [search_cost_iff (constant_after_returns c G),
    final_cost_iff (show (Combined.machine 1 [.term] (environmentInterface 0 0 ++ O)).final
      ⟨after (constantBody c) G,(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,zero⟩; omega
  · rintro rfl; exact ⟨1,rfl,0,rfl,rfl⟩

theorem nested_cost_iff {O} (G : Hypernet 2 [.term] O) (stable : Stable G) (cost : Nat) :
    TerminatesIn cost ⟨before nestedBody G,(.search,.input 0)⟩ ↔ cost = 7 := by
  rw [opening_cost_iff _ _ stable]
  simp only [search_cost_iff (nested_after_returns G),
    final_cost_iff (show (Combined.machine 2 [.term] (environmentInterface 0 0 ++ O)).final
      ⟨after nestedBody G,(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,zero⟩; omega
  · rintro rfl; exact ⟨1,rfl,0,rfl,rfl⟩

/-- The translated variable still requests copying. Its cost is seven plus the
cost of the actual remaining copying computation, without a termination premise. -/
theorem variable_cost_iff {O} (G : Hypernet 1 [.term] O) (stable : Stable G) (cost : Nat) :
    TerminatesIn cost ⟨before variableBody G,(.search,.input 0)⟩ ↔
      ∃ rest, cost = rest+7 ∧ TerminatesIn rest ⟨after variableBody G,(.rewrite,.input 0)⟩ := by
  rw [opening_cost_iff _ _ stable]
  simp only [search_cost_iff (variable_after_requests_copy G)]
  constructor
  · rintro ⟨a,ha,b,hb,run⟩; exact ⟨b,by omega,run⟩
  · rintro ⟨rest,rfl,run⟩; exact ⟨rest+1,rfl,rest,rfl,run⟩

/-- Reaching the copy request is not successful termination. -/
theorem variable_no_early_success {O} (G : Hypernet 1 [.term] O) (stable : Stable G) (cost : Nat) (early : cost ≤ 7) :
    ¬ TerminatesIn cost ⟨before variableBody G,(.search,.input 0)⟩ := by
  intro run
  obtain ⟨rest,eq,t,run,done⟩ := (variable_cost_iff G stable cost).mp run
  have zero : rest = 0 := by omega
  subst rest
  cases run
  cases done.1

/-- The atom attachment of a reference argument does not change the exact successful cost. -/
theorem reference_argument_cost_iff (cost : Nat) :
    TerminatesIn cost ⟨before (constantBody (.nat 1)) (primitiveNet 1 .instanceEdge),(.search,.input 0)⟩ ↔ cost = 7 :=
  constant_cost_iff _ _ (Stable.instanceEdge 1) cost

/-- The full unbounded application example has exactly this cost at every finite padding. -/
theorem constant_pad_cost_iff (c : Constant) (layers cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial ((Combined.Examples.applicationProgram c).pad layers)) t ∧
      unboundedMachine.final t) ↔ cost = 7 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  exact constant_cost_iff c _ (Stable.constant 1 .unit) cost
end Hypernets.Copying.Application.Examples
