import Hypernets.Copying.CombinedEmbedding

/-! Original translated allocation and a surrounding active operation now execute
in one contextual subsystem. Internal returns are checked against false finality. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined.Examples
open Graph

/-- The actual Figure 16 translation of ref n, with all original distributors. -/
def referenceProgram (n : Nat) : ClosedProgram where
  depth := 0
  graph := Allocation.referenceGraph n
  focusFree := Translation.term_focusFree _
  holeFree := Translation.term_holeFree _

theorem reference_run (n : Nat) :
    unboundedMachine.Steps 5 (execution.initial (referenceProgram n))
      ⟨0,Allocation.allocatedGraph n,(.backtrack,.input 0)⟩ :=
  run_unbounded (allocation_run (Allocation.reference_run n))

theorem reference_terminates (n : Nat) : execution.Terminates (referenceProgram n) :=
  ⟨5,⟨0,Allocation.allocatedGraph n,(.backtrack,.input 0)⟩,reference_run n,rfl,trivial⟩

/-- Arbitrary recursive carrier renaming preserves all successful costs, not just existence. -/
theorem reference_representation (n : Nat) (H : Hypernet 0 [.term] [])
    (f : DeepIso (Allocation.referenceGraph n) H) (hf : FocusFree H) (hh : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact (execution.initial (referenceProgram n))
      (execution.initial ⟨0,H,hf,hh⟩) :=
  represents_equiv CostOrder.exact (.lift {graph := f, mode := rfl, vertex := rfl})

def outerRef : Hypernet 0 [.term] [.term] := primitiveNet 0 (.operation (.unary .ref))
def nested (n : Nat) := Serial.net outerRef (Allocation.referenceGraph n)
def nestedAllocated (n : Nat) := Serial.net outerRef (Allocation.allocatedGraph n)
def innerInput (H : Hypernet 0 [.term] []) : (Serial.net outerRef H).Vertex :=
  BoundarySerial.rightInsert outerRef H (.input 0)

theorem enter_inner (n : Nat) :
    Search.Step (nested n) (.search,.input 0) (.search,innerInput (Allocation.referenceGraph n)) := by
  apply Search.Step.search (G := nested n) ⟨false,(0 : Fin 1)⟩ (.operation (.unary .ref)) _ _ rfl
  · change (.input 0 : (nested n).Vertex) ∈ [.input 0]; exact List.mem_cons_self
  · rfl

theorem return_to_outer (n : Nat) :
    Search.Step (nestedAllocated n) (.backtrack,innerInput (Allocation.allocatedGraph n))
      (.rewrite,.input 0) :=
  .backtrack (G := nestedAllocated n) ⟨false,(0 : Fin 1)⟩ (.unary .ref) (.input 0) _ 0 _ rfl rfl (by decide) rfl rfl

/-- An actual compute inside an active argument, followed by resuming the host search. -/
theorem nested_run (n : Nat) :
    (machine 0 [.term] []).Steps 7 ⟨nested n,(.search,.input 0)⟩
      ⟨nestedAllocated n,(.rewrite,.input 0)⟩ := by
  have inner := run_serialRight outerRef (allocation_run (Allocation.reference_run n))
  exact (Machine.Steps.cons (M := machine 0 [.term] []) (Step.search _ (enter_inner n)) inner).append
    (.cons (.search _ (return_to_outer n)) (.zero _))

/-- Returning from the inserted ref does not incorrectly terminate the outer ref. -/
theorem inner_return_not_final (n : Nat) :
    ¬ (machine 0 [.term] []).final
      ⟨nestedAllocated n,(.backtrack,innerInput (Allocation.allocatedGraph n))⟩ :=
  right_return_not_final outerRef (Allocation.allocatedGraph n) 0

/-- The seven-step endpoint requests another allocation; it is not a final value. -/
theorem nested_endpoint_not_final (n : Nat) :
    ¬ (machine 0 [.term] []).final ⟨nestedAllocated n,(.rewrite,.input 0)⟩ := by
  intro done; cases done.1

/-- A literal translated constant body with an unused parameter and a unit argument. -/
def applicationProgram (c : Constant) : ClosedProgram where
  depth := 1
  graph := Application.before (Application.Examples.constantBody c) (primitiveNet 1 (.operation (.const .unit)))
  focusFree := (Application.safe_sides _ _ (Translation.term_focusFree _) (Translation.term_holeFree _)
    (Stable.constant 1 .unit)).1
  holeFree := (Application.safe_sides _ _ (Translation.term_focusFree _) (Translation.term_holeFree _)
    (Stable.constant 1 .unit)).2.1

theorem application_run (c : Constant) :
    unboundedMachine.Steps 7 (execution.initial (applicationProgram c))
      ⟨1,Application.after (Application.Examples.constantBody c) (primitiveNet 1 (.operation (.const .unit))),
        (.backtrack,.input 0)⟩ :=
  run_unbounded (Combined.application_run (Application.Examples.constant_run c _ (Stable.constant 1 .unit)))

theorem application_terminates (c : Constant) : execution.Terminates (applicationProgram c) :=
  ⟨7,_,application_run c,rfl,trivial⟩
end Hypernets.Copying.Combined.Examples
