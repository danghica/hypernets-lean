import Hypernets.Copying.FullRefocusing

/-! Refocusing regressions through nested operation hosts, deleting frames and unchanged translations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined.FullRefocusingExamples
open Graph

def unaryHost (d : Nat) (o : Unary) : Hypernet d [.term] [.term] :=
  primitiveNet d (.operation (.unary o))

/-- An actual unary host searches its argument at an internal wire. -/
theorem unary_enters {d O} (o : Unary) (G : Hypernet d [.term] O) :
    Search.Step (Serial.net (unaryHost d o) G) (.search,.input 0)
      (.search,BoundarySerial.rightInsert (unaryHost d o) G (.input 0)) := by
  cases d <;> apply Search.Step.search (G := Serial.net (unaryHost _ o) G)
    ⟨false,(0 : Fin 1)⟩ (.operation (.unary o)) _ _ rfl
  all_goals first | exact List.mem_cons_self | rfl

/-- Opening a complete lambda body below an active reference host preserves its internal root. -/
theorem application_host_rooted {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    Search.RootedFrom (Serial.net (unaryHost (d+1) .ref) (Application.after B G)) 0
      (.search,BoundarySerial.rightInsert (unaryHost (d+1) .ref)
        (Application.after B G) (.input 0)) := by
  have tail := run_serialRight (unaryHost (d+1) .ref)
    (application_run (Application.opening_run B G stable))
  have run := Machine.Steps.cons (M := machine (d+1) [.term] (environmentInterface k h ++ O))
    (Step.search _ (unary_enters .ref (Application.before B G))) tail
  exact run_rootedFrom run (Search.rooted_initial (Serial.net (unaryHost (d+1) .ref) (Application.before B G)) 0)

/-- The original nested-lambda translation remains searchable after opening inside a host. -/
theorem nested_lambda_host_rooted :
    Rooted (serialRight (unaryHost 2 .ref)
      ⟨Application.after Application.Examples.nestedBody (primitiveNet 2 (.operation (.const .unit))),
        (.search,.input 0)⟩) :=
  application_host_rooted _ _ (Stable.constant 2 .unit)

/-- The original variable-body translation still produces a rooted internal copying request. -/
theorem variable_host_copy_rooted :
    Rooted (serialRight (unaryHost 1 .ref)
      ⟨Application.after Application.Examples.variableBody (primitiveNet 1 (.operation (.const .unit))),
        (.rewrite,.input 0)⟩) := by
  exact Search.rooted_step (application_host_rooted _ _ (Stable.constant 1 .unit))
    (Search.serial_right _ (Application.Examples.variable_after_requests_copy _))

/-- A deleting arithmetic rewrite returns to a rooted internal token, before the outer operation runs. -/
theorem arithmetic_host_return_rooted (o : Arithmetic.BinaryCode) (m n : Nat) :
    Rooted (serialRight (unaryHost 0 .neg)
      ⟨Arithmetic.binaryAfter o 0 m n,(.backtrack,.input 0)⟩) := by
  have tail := run_serialRight (unaryHost 0 .neg) (Arithmetic.binary_run o 0 m n)
  have run := Machine.Steps.cons (M := machine 0 [.term] [])
    (Step.search _ (unary_enters .neg (Arithmetic.binaryBefore o 0 m n))) tail
  exact run_rootedFrom run (Search.rooted_initial (Serial.net (unaryHost 0 .neg) (Arithmetic.binaryBefore o 0 m n)) 0)

theorem arithmetic_host_return_not_final (o : Arithmetic.BinaryCode) (m n : Nat) :
    ¬ (machine 0 [.term] []).final (serialRight (unaryHost 0 .neg)
      ⟨Arithmetic.binaryAfter o 0 m n,(.backtrack,.input 0)⟩) :=
  right_return_not_final (unaryHost 0 .neg) (Arithmetic.binaryAfter o 0 m n) 0

/-- Arbitrary old translated contents, including omega, need not run for a rooted write to terminate. -/
theorem overwrite_rooted_result (t : Term 0 0) (c : Constant) (layers : Nat) :
    ∃ s, unboundedMachine.Steps 7 (execution.initial ((AssignmentCoherenceExamples.storedTerm t c).pad layers)) s ∧
      unboundedMachine.final s ∧ UnboundedRooted s := by
  obtain ⟨s,run,done⟩ := (AssignmentCoherenceExamples.storedTerm_exact_cost t c layers 7).mpr rfl
  exact ⟨s,run,done,execution_rooted _ run⟩

/-- Both reference-identity branches terminate at rooted states with unchanged translated contents. -/
theorem equality_rooted_results (t : Term 0 0) (layers : Nat) :
    (∃ s, unboundedMachine.Steps 7
      (execution.initial ((EqualityCoherenceExamples.sharedContents t).pad layers)) s ∧
      unboundedMachine.final s ∧ UnboundedRooted s) ∧
    (∃ s, unboundedMachine.Steps 7
      (execution.initial ((EqualityCoherenceExamples.distinctContents t).pad layers)) s ∧
      unboundedMachine.final s ∧ UnboundedRooted s) := by
  constructor
  · obtain ⟨s,run,done⟩ := (EqualityCoherenceExamples.shared_exact_cost t layers 7).mpr rfl
    exact ⟨s,run,done,execution_rooted _ run⟩
  · obtain ⟨s,run,done⟩ := (EqualityCoherenceExamples.distinct_exact_cost t layers 7).mpr rfl
    exact ⟨s,run,done,execution_rooted _ run⟩

end Hypernets.Copying.Combined.FullRefocusingExamples
