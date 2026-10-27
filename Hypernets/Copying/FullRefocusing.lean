import Hypernets.Copying.ArithmeticRefocusing

/-! Unconditional refocusing of the original full finite and unbounded copying machine. -/
namespace Hypernets.Copying.Combined

/-- Every actual contextual rewrite preserves rootedness on its complete successor graph. -/
theorem rewrite_rooted {d I O} {G H : Hypernet d I O} {v w i}
    (step : Rewrite G v H w) (root : Search.RootedFrom G i (.rewrite,v)) :
    Search.RootedFrom H i (.search,w) := by
  obtain ⟨choice,recognized⟩ := rewrite_recognizes step
  have witness := recognized
  obtain ⟨e,head,_⟩ := witness
  cases choice with
  | allocate => exact allocation_rooted head step root
  | read => exact dereference_rooted head step root
  | assign => exact assignment_rooted head step root
  | compare b => exact equality_rooted head step root
  | beta => exact application_rooted head step root
  | copy p => exact copying_rooted head step root
  | neg n => exact arithmetic_rooted (.neg n) recognized step root
  | binary o m n => exact arithmetic_rooted (.binary o m n) recognized step root

/-- Full refocusing holds from any specified external input, without a compute-law premise. -/
theorem step_rootedFrom {d I O} {s t : State d I O} {i}
    (step : Step s t) (root : Search.RootedFrom s.1 i s.2) : Search.RootedFrom t.1 i t.2 := by
  cases step with
  | search G step => exact Search.rooted_step root step
  | rewrite step => exact rewrite_rooted step root

/-- The finite copying UAM is refocusing for its original complete operation set. -/
theorem refocusing {d} : Refocusing (@Step d [.term] []) := by
  intro s t root step
  exact step_rootedFrom step root

/-- Every finite execution preserves rootedness from the same external input. -/
theorem run_rootedFrom {d I O} {s t : State d I O} {i n}
    (run : (machine d I O).Steps n s t) (root : Search.RootedFrom s.1 i s.2) :
    Search.RootedFrom t.1 i t.2 := by
  induction run with
  | zero => exact root
  | cons step run ih => exact ih (step_rootedFrom step root)

/-- The full unbounded copying UAM is refocusing, with no extrinsic-law assumptions. -/
theorem unbounded_refocusing : UnboundedRefocusing UnboundedStep := by
  intro s t root step
  cases step with | lift step => exact refocusing root step

/-- Rootedness holds at the endpoint of every actual unbounded run from a rooted state. -/
theorem unbounded_run_rooted {s t : UnboundedState} {n}
    (run : unboundedMachine.Steps n s t) (root : UnboundedRooted s) : UnboundedRooted t := by
  induction run with
  | zero => exact root
  | cons step run ih => exact ih (unbounded_refocusing root step)

/-- Every state reached from any closed program is rooted on its own current graph. -/
theorem execution_rooted (P : ClosedProgram) {n t}
    (run : execution.machine.Steps n (execution.initial P) t) : UnboundedRooted t :=
  unbounded_run_rooted run (initial_rooted P)

/-- Every prefix of a possibly nonterminating execution satisfies rootedness. -/
theorem infinite_run_rooted (P : ClosedProgram) (states : Nat → UnboundedState)
    (initial : states 0 = execution.initial P) (steps : ∀ n, UnboundedStep (states n) (states (n+1))) :
    ∀ n, UnboundedRooted (states n) := by
  intro n
  induction n with
  | zero => rw [initial]; exact initial_rooted P
  | succ n ih => exact unbounded_refocusing ih (steps n)
end Hypernets.Copying.Combined
