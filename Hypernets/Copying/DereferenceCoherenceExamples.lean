import Hypernets.Copying.DereferenceCost

/-! Full-machine read regressions preserve translated data and the pending copy request. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.DereferenceCoherenceExamples
open Graph Combined

/-- A closed read with an arbitrary unchanged term translation as stored data. -/
def storedTerm (t : Term 0 0) : ClosedProgram where
  depth := Translation.depth t
  graph := Serial.net (Dereference.before (ContractionTree.canonical .atom 1) (Translation.depth t))
    (Translation.term t)
  focusFree := Serial.focusFree_net (Dereference.focusFree_sides _ _).1 (Translation.term_focusFree t)
  holeFree := Serial.holeFree_net (Dereference.holeFree_sides _ _).1 (Translation.term_holeFree t)

/-- The concrete post-read state still requests copying; it retains the original data graph. -/
def pending (t : Term 0 0) : Combined.State (Translation.depth t) [.term] [] :=
  serialLeft (Translation.term t)
    ⟨Dereference.after (ContractionTree.canonical .atom 1) (Translation.depth t),
      (.rewrite,Dereference.inputPort 0 0)⟩

/-- All padded successful executions have exactly the five-step read prefix and a
successful continuation from the actual copying request. -/
theorem storedTerm_cost_handoff (t : Term 0 0) (layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost (execution.initial ((storedTerm t).pad layers)) s ∧
      unboundedMachine.final s) ↔ ∃ rest, cost = rest+5 ∧ TerminatesIn rest (pending t) := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  have h := Dereference.contents_cost_handoff (ContractionTree.canonical .atom 1) (Translation.term t) cost
  simpa only [serialLeft,Dereference.inputPort,left_input,storedTerm,pending,execution,Fin.val_zero,
    Dereference.inputs,environmentInterface,List.replicate_zero,List.nil_append,List.length_cons,
    List.length_nil,Fin.zero_eta] using h

/-- The unbounded full machine can perform the entire prefix without evaluating the data. -/
theorem storedTerm_prefix (t : Term 0 0) :
    unboundedMachine.Steps 5 (execution.initial (storedTerm t)) ⟨Translation.depth t,pending t⟩ := by
  have h := run_unbounded (Dereference.contents_prefix (ContractionTree.canonical .atom 1) (Translation.term t))
  simpa only [serialLeft,Dereference.inputPort,left_input,storedTerm,pending,execution,Fin.val_zero,
    Dereference.inputs,environmentInterface,List.replicate_zero,List.nil_append,List.length_cons,
    List.length_nil,Fin.zero_eta] using h

/-- Padding cannot turn the unfinished read prefix into a returned value. -/
theorem storedTerm_no_early_success (t : Term 0 0) (layers cost : Nat) (early : cost ≤ 5) :
    ¬ ∃ s, unboundedMachine.Steps cost (execution.initial ((storedTerm t).pad layers)) s ∧
      unboundedMachine.final s := by
  intro run
  obtain ⟨rest,eq,s,steps,done⟩ := (storedTerm_cost_handoff t layers cost).mp run
  have zero : rest = 0 := by omega
  subst rest
  cases steps
  cases done.1

/-- Even a literal retains its full distributor and needs the subsequent copying execution. -/
theorem literal_cost_handoff (value layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost
      (execution.initial ((storedTerm (.const (.nat value))).pad layers)) s ∧
      unboundedMachine.final s) ↔
    ∃ rest, cost = rest+5 ∧ TerminatesIn rest (pending (.const (.nat value))) :=
  storedTerm_cost_handoff _ layers cost

/-- The nested boxes of literal omega are retained through the read. This is a prefix
and continuation law, not a theorem that evaluation of omega diverges or terminates. -/
theorem omega_cost_handoff (layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost
      (execution.initial ((storedTerm Examples.omegaTerm).pad layers)) s ∧
      unboundedMachine.final s) ↔
    ∃ rest, cost = rest+5 ∧ TerminatesIn rest (pending Examples.omegaTerm) :=
  storedTerm_cost_handoff _ layers cost

/-- Every actual read successor preserves the entire unchanged translated payload. -/
theorem storedTerm_successor (t : Term 0 0) {s}
    (step : Combined.Step (serialLeft (Translation.term t)
      ⟨Dereference.before (ContractionTree.canonical .atom 1) (Translation.depth t),
        (.rewrite,Dereference.inputPort 0 0)⟩) s) :
    Nonempty (StateIso s (serialLeft (Translation.term t)
      ⟨Dereference.after (ContractionTree.canonical .atom 1) (Translation.depth t),
        (.search,Dereference.inputPort 0 0)⟩)) :=
  Dereference.contents_successor _ _ step
end Hypernets.Copying.DereferenceCoherenceExamples
