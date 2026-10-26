import Hypernets.Copying.ArithmeticCost

/-! Full-machine, all-run arithmetic regressions, with exact costs at every padding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic.Examples
open Graph Combined

/-- Every successful padded unary execution has cost five; such an execution exists. -/
theorem unary_pad_cost_iff (d n layers cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial ((unaryProgram d n).pad layers)) t ∧
      unboundedMachine.final t) ↔ cost = 5 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  exact unary_cost_iff d n cost

/-- Every successful padded binary execution has cost seven, independently of matching. -/
theorem binary_pad_cost_iff (o : BinaryCode) (d m n layers cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial ((binaryProgram o d m n).pad layers)) t ∧
      unboundedMachine.final t) ↔ cost = 7 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  exact binary_cost_iff o d m n cost

/-- Natural subtraction underflow changes the result, not the cost or termination spectrum. -/
theorem underflow_result_and_cost (d m n layers : Nat) (le : m ≤ n) :
    (machine d [.term] []).Steps 7 ⟨binaryBefore .sub d m n,(.search,.input 0)⟩
      ⟨number d 0,(.backtrack,.input 0)⟩ ∧
    ∀ cost, (∃ t, unboundedMachine.Steps cost
      (execution.initial ((binaryProgram .sub d m n).pad layers)) t ∧ unboundedMachine.final t) ↔ cost = 7 :=
  ⟨subtraction_underflow d m n le,binary_pad_cost_iff .sub d m n layers⟩

/-- Unary negation is the agreed natural-number operation 0-n, with its full exact cost. -/
theorem negation_result_and_cost (d n layers : Nat) :
    (machine d [.term] []).Steps 5 ⟨unaryBefore d n,(.search,.input 0)⟩
      ⟨number d 0,(.backtrack,.input 0)⟩ ∧
    ∀ cost, (∃ t, unboundedMachine.Steps cost
      (execution.initial ((unaryProgram d n).pad layers)) t ∧ unboundedMachine.final t) ↔ cost = 5 :=
  ⟨unary_result d n,unary_pad_cost_iff d n layers⟩

/-- Any arithmetic evaluation attached below a host has an exact seven-step handoff
back to that host. The host can continue running, diverge, or get stuck. -/
theorem binary_host_handoff {d I} (C : Hypernet d I [.term]) (o : BinaryCode) (m n cost : Nat) :
    TerminatesIn cost (serialRight C ⟨binaryBefore o d m n,(.search,.input 0)⟩) ↔
      ∃ rest, cost = rest+7 ∧ TerminatesIn rest (serialRight C ⟨binaryAfter o d m n,(.backtrack,.input 0)⟩) := by
  have compute (k : Nat) := arithmetic_cost_spectrum (.binary o m n)
    (recognizes_map (MatchEmbedding.serialRight C (binaryBefore o d m n))
      ⟨binaryHead o d m n,binary_head o d m n,binary_left_operand o d m n,binary_right_operand o d m n⟩)
    (step_serialRight C (rule_step (.binary o m n))) k
  dsimp only [MatchEmbedding.serialRight,serialRight] at compute
  unfold serialRight
  rw [search_cost_iff (Search.serial_right C (binary_enter o d m n))]
  simp only [search_cost_iff (Search.serial_right C (binary_left_returns o d m n)),
    search_cost_iff (Search.serial_right C (binary_search_right o d m n)),
    search_cost_iff (Search.serial_right C (binary_right_returns o d m n)),
    search_cost_iff (Search.serial_right C (binary_ready o d m n)),compute,binaryAfter,
    search_cost_iff (Search.serial_right C (number_returns d (o.eval m n)))]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,g,hg,h,hh,run⟩; exact ⟨h,by omega,run⟩
  · rintro ⟨rest,rfl,run⟩
    exact ⟨rest+6,by omega,rest+5,by omega,rest+4,by omega,rest+3,by omega,
      rest+2,by omega,rest+1,by omega,rest,rfl,run⟩

/-- A nested arithmetic expression has only the expected eleven-step successful cost.
The inner computation changes the graph before the outer operation resumes. -/
theorem nested_cost_iff (o : BinaryCode) (m n cost : Nat) :
    TerminatesIn cost ⟨nested o m n,(.search,.input 0)⟩ ↔ cost = 11 := by
  have inner (k : Nat) := binary_host_handoff (primitiveNet 0 (.operation (.unary .neg))) o m n k
  rw [search_cost_iff (nested_enter o m n)]
  dsimp only [serialRight] at inner
  change (∃ a, cost = a+1 ∧ TerminatesIn a (serialRight _ ⟨binaryBefore o 0 m n,(.search,.input 0)⟩)) ↔ _
  simp only [serialRight,inner]
  change (∃ a, cost = a+1 ∧ ∃ rest, a = rest+7 ∧
    TerminatesIn rest ⟨unaryBefore 0 (o.eval m n),(.backtrack,unaryArgument 0 (o.eval m n))⟩) ↔ _
  simp only [search_cost_iff (unary_ready 0 (o.eval m n)),
    arithmetic_cost_spectrum (.neg (o.eval m n))
      ⟨unaryHead 0 (o.eval m n),unary_head 0 (o.eval m n),unary_operand 0 (o.eval m n)⟩
      (rule_step (.unary (o.eval m n))),unaryAfter,
    search_cost_iff (number_returns 0 (neg (o.eval m n))),
    final_cost_iff (show (machine 0 [.term] []).final
      ⟨number 0 (neg (o.eval m n)),(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,zero⟩; omega
  · rintro rfl; exact ⟨10,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩
end Hypernets.Copying.Arithmetic.Examples
