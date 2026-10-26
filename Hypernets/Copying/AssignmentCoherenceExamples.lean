import Hypernets.Copying.AssignmentCost

/-! Full-machine write regressions, retaining the original translations as heap data. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AssignmentCoherenceExamples
open Graph Combined

/-- A write of a stable constant over arbitrary, unchanged translated old contents. -/
def storedTerm (t : Term 0 0) (c : Constant) : ClosedProgram where
  depth := Translation.depth t
  graph := Serial.net (Assignment.before (ContractionTree.canonical .atom 1)
    (primitiveNet (Translation.depth t) (.operation (.const c)))) (Translation.term t)
  focusFree := Serial.focusFree_net
    (Assignment.stable_assignment_safe _ _ (Stable.constant _ _)).1 (Translation.term_focusFree t)
  holeFree := Serial.holeFree_net
    (Assignment.stable_assignment_safe _ _ (Stable.constant _ _)).2.1 (Translation.term_holeFree t)

/-- Every successful execution costs seven, even with arbitrary old data and depth padding. -/
theorem storedTerm_exact_cost (t : Term 0 0) (c : Constant) (layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost (execution.initial ((storedTerm t c).pad layers)) s ∧
      unboundedMachine.final s) ↔ cost = 7 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  have h := Assignment.contents_exact_cost (ContractionTree.canonical .atom 1)
    (primitiveNet (Translation.depth t) (.operation (.const c))) (Stable.constant _ _)
    (Translation.term t) cost
  simpa only [serialLeft,Assignment.inputPort,left_input,storedTerm,execution,Fin.val_zero,
    Assignment.inputs,environmentInterface,List.replicate_zero,List.nil_append,List.length_cons,
    List.length_nil,Fin.zero_eta] using h

/-- Both the new and old payloads are the literal Figure 16 translations, without contraction. -/
def translatedLiterals (old new : Nat) : ClosedProgram where
  depth := 0
  graph := Serial.net (Assignment.before (ContractionTree.canonical .atom 1)
    (Allocation.constantArgument new)) (Allocation.constantArgument old)
  focusFree := Serial.focusFree_net
    (Assignment.stable_assignment_safe _ _ (Allocation.constantArgument_stable new)).1
    (Allocation.constantArgument_stable old).focusFree
  holeFree := Serial.holeFree_net
    (Assignment.stable_assignment_safe _ _ (Allocation.constantArgument_stable new)).2.1
    (Allocation.constantArgument_stable old).holeFree

/-- The exact cost law also applies when the new value retains its full term translation. -/
theorem translatedLiterals_exact_cost (old new layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost (execution.initial ((translatedLiterals old new).pad layers)) s ∧
      unboundedMachine.final s) ↔ cost = 7 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  have h := Assignment.contents_exact_cost (ContractionTree.canonical .atom 1)
    (Allocation.constantArgument new) (Allocation.constantArgument_stable new)
    (Allocation.constantArgument old) cost
  simpa only [serialLeft,Assignment.inputPort,left_input,translatedLiterals,execution,Fin.val_zero,
    Assignment.inputs,environmentInterface,List.replicate_zero,List.nil_append,List.length_cons,
    List.length_nil,Fin.zero_eta] using h

/-- Writing does not run the literal omega translation in the old cell. This theorem
asserts the write's cost; it does not assert a divergence theorem for omega itself. -/
theorem overwrite_omega (layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost
      (execution.initial ((storedTerm Examples.omegaTerm (.nat 1)).pad layers)) s ∧
      unboundedMachine.final s) ↔ cost = 7 := storedTerm_exact_cost _ _ layers cost

/-- Full successor coherence applies to the explicitly retained old and new literal graphs. -/
theorem translatedLiterals_successor (old new : Nat) {s}
    (step : Combined.Step (serialLeft (Allocation.constantArgument old)
      ⟨Assignment.before (ContractionTree.canonical .atom 1) (Allocation.constantArgument new),
        (.rewrite,Assignment.inputPort 0 [] 0)⟩) s) :
    Nonempty (StateIso s (serialLeft (Allocation.constantArgument old)
      ⟨Assignment.after (ContractionTree.canonical .atom 1) (Allocation.constantArgument new),
        (.search,Assignment.inputPort 0 [] 0)⟩)) :=
  Assignment.contents_successor _ _ (Allocation.constantArgument_stable new) _ step
end Hypernets.Copying.AssignmentCoherenceExamples
