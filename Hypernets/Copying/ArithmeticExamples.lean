import Hypernets.Copying.ArithmeticExecution
import Hypernets.Copying.CombinedExamples

/-! Numeric boundary cases, actual contextual computation and arbitrary padding.
The original term translation is unchanged; local arithmetic redexes are named explicitly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic.Examples
open Graph

/-- Local arithmetic redex programs at arbitrary allowances. -/
def unaryProgram (d n : Nat) : ClosedProgram :=
  ⟨d,unaryBefore d n,Translation.language_focusFree (unary_language d n),
    Translation.language_holeFree (unary_language d n)⟩

def binaryProgram (o : BinaryCode) (d m n : Nat) : ClosedProgram :=
  ⟨d,binaryBefore o d m n,Translation.language_focusFree (binary_language o d m n),
    Translation.language_holeFree (binary_language o d m n)⟩

theorem unary_terminates (d n : Nat) : Combined.execution.Terminates (unaryProgram d n) :=
  ⟨5,⟨d,unaryAfter d n,(.backtrack,.input 0)⟩,Combined.run_unbounded (unary_run d n),rfl,trivial⟩

theorem binary_terminates (o : BinaryCode) (d m n : Nat) : Combined.execution.Terminates (binaryProgram o d m n) :=
  ⟨7,⟨d,binaryAfter o d m n,(.backtrack,.input 0)⟩,Combined.run_unbounded (binary_run o d m n),rfl,trivial⟩

/-- Unary minus is zero minus n in the original Nat-valued constant domain. -/
theorem unary_result (d n : Nat) :
    (Combined.machine d [.term] []).Steps 5 ⟨unaryBefore d n,(.search,.input 0)⟩
      ⟨number d 0,(.backtrack,.input 0)⟩ := by
  have run := unary_run d n
  have eq := congrArg (fun k => (⟨number d k,(.backtrack,.input 0)⟩ : Combined.State d [.term] [])) (neg_eq_zero n)
  change (Combined.machine d [.term] []).Steps 5 _ ⟨number d (neg n),(.backtrack,.input 0)⟩ at run
  rw [eq] at run
  exact run

/-- Exact underflow behaviour is tested for every pair m ≤ n, not only small numerals. -/
theorem subtraction_underflow (d m n : Nat) (le : m ≤ n) :
    (Combined.machine d [.term] []).Steps 7 ⟨binaryBefore .sub d m n,(.search,.input 0)⟩
      ⟨number d 0,(.backtrack,.input 0)⟩ := by
  have run := binary_run .sub d m n
  have eq := congrArg (fun k => (⟨number d k,(.backtrack,.input 0)⟩ : Combined.State d [.term] [])) (Nat.sub_eq_zero_of_le le)
  change (Combined.machine d [.term] []).Steps 7 _ ⟨number d (m-n),(.backtrack,.input 0)⟩ at run
  rw [eq] at run
  exact run

theorem addition_zero (d n : Nat) :
    (Combined.machine d [.term] []).Steps 7 ⟨binaryBefore .add d n 0,(.search,.input 0)⟩
      ⟨number d n,(.backtrack,.input 0)⟩ := by
  simpa only [binaryAfter,BinaryCode.eval,Nat.add_zero] using binary_run .add d n 0

theorem subtraction_zero (d n : Nat) :
    (Combined.machine d [.term] []).Steps 7 ⟨binaryBefore .sub d n 0,(.search,.input 0)⟩
      ⟨number d n,(.backtrack,.input 0)⟩ := by
  simpa only [binaryAfter,BinaryCode.eval,Nat.sub_zero] using binary_run .sub d n 0

/-- An outer operation whose argument really changes graph before the outer rewrite. -/
def nested (o : BinaryCode) (m n : Nat) : Hypernet 0 [.term] [] :=
  Serial.net (primitiveNet 0 (.operation (.unary .neg))) (binaryBefore o 0 m n)

def innerInput (o : BinaryCode) (m n : Nat) : (nested o m n).Vertex :=
  BoundarySerial.rightInsert (primitiveNet 0 (.operation (.unary .neg))) (binaryBefore o 0 m n) (.input (0 : Fin 1))

theorem nested_enter (o : BinaryCode) (m n : Nat) :
    Search.Step (nested o m n) (.search,.input 0) (.search,innerInput o m n) := by
  apply Search.Step.search (G := nested o m n) ⟨false,(0 : Fin 1)⟩ (.operation (.unary .neg)) _ _ rfl
  · exact List.mem_cons_self
  · rfl

/-- One entry, seven inner steps, one resume, one outer rewrite and one return. -/
theorem nested_run (o : BinaryCode) (m n : Nat) :
    (Combined.machine 0 [.term] []).Steps 11 ⟨nested o m n,(.search,.input 0)⟩
      ⟨unaryAfter 0 (o.eval m n),(.backtrack,.input 0)⟩ := by
  have inner := Combined.run_serialRight (primitiveNet 0 (.operation (.unary .neg))) (binary_run o 0 m n)
  have firstRun := Machine.Steps.cons (M := Combined.machine 0 [.term] [])
    (Combined.Step.search _ (nested_enter o m n)) inner
  exact firstRun.append (.cons (.search _ (unary_ready 0 (o.eval m n)))
    (.cons (rule_step (.unary (o.eval m n))) (.cons (.search _ (number_returns 0 (neg (o.eval m n)))) (.zero _))))

/-- The same original translated ref program still terminates at every higher allowance. -/
theorem translated_reference_pad (value allowance : Nat) :
    Combined.execution.Terminates ((Combined.Examples.referenceProgram value).pad allowance) :=
  Combined.terminates_pad _ _ (Combined.Examples.reference_terminates value)

/-- Original translated lambda bodies retain their seven-step successful cost after padding. -/
theorem application_pad_cost (c : Constant) (allowance : Nat) :
    ∃ t, Combined.unboundedMachine.Steps 7
      (Combined.execution.initial ((Combined.Examples.applicationProgram c).pad allowance)) t ∧
      Combined.unboundedMachine.final t := by
  obtain ⟨n,t,cost,run,final⟩ :=
    Combined.initial_pad_refines CostOrder.exact (Combined.Examples.applicationProgram c) allowance
      (Combined.Examples.application_run c) ⟨rfl,trivial⟩
  cases cost
  exact ⟨t,run,final⟩

/-- Arbitrarily many unused box layers preserve arithmetic costs, too. -/
theorem binary_pad_cost (o : BinaryCode) (d m n allowance : Nat) :
    ∃ t, Combined.unboundedMachine.Steps 7
      (Combined.execution.initial ((binaryProgram o d m n).pad allowance)) t ∧
      Combined.unboundedMachine.final t := by
  obtain ⟨q,t,cost,run,final⟩ :=
    Combined.initial_pad_refines CostOrder.exact (binaryProgram o d m n) allowance
      (Combined.run_unbounded (binary_run o d m n)) ⟨rfl,trivial⟩
  cases cost
  exact ⟨t,run,final⟩
end Hypernets.Copying.Arithmetic.Examples
