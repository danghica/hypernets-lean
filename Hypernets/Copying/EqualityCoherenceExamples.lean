import Hypernets.Copying.EqualityCost
import Hypernets.Copying.FullTranslationExamples

/-! Full-machine regression scenarios with the unchanged term translation as store contents. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined

/-- Successful costs of an unbounded state are exactly those of its bounded representative. -/
theorem successful_unbounded_iff {d} (s : State d [.term] []) (cost : Nat) :
    (∃ t, unboundedMachine.Steps cost ⟨d,s⟩ t ∧ unboundedMachine.final t) ↔ TerminatesIn cost s := by
  constructor
  · rintro ⟨t,run,done⟩
    obtain ⟨b,eq,small⟩ := run_bounded run s rfl
    subst t
    exact ⟨b,small,done⟩
  · rintro ⟨t,run,done⟩
    exact ⟨⟨d,t⟩,run_unbounded run,done⟩
end Hypernets.Copying.Combined

namespace Hypernets.Copying.EqualityCoherenceExamples
open Graph Combined

/-- A shared reference to an arbitrary translated closed term, with a noncanonical tree. -/
def sharedContents (t : Term 0 0) : ClosedProgram where
  depth := Translation.depth t
  graph := Serial.net (AtomEquality.Same.before (Examples.binaryTree .atom) (Translation.depth t))
    (Translation.term t)
  focusFree := Serial.focusFree_net (AtomEquality.Same.focusFree_sides _ _).1 (Translation.term_focusFree t)
  holeFree := Serial.holeFree_net (AtomEquality.Same.holeFree_sides _ _).1 (Translation.term_holeFree t)

/-- Two different references to two unchanged copies of the same translated closed term. -/
def distinctContents (t : Term 0 0) : ClosedProgram where
  depth := Translation.depth t
  graph := Serial.net (AtomEquality.Different.before (ContractionTree.canonical .atom 1)
      (ContractionTree.canonical .atom 1) (Translation.depth t))
    (Net.Tensor.net (Translation.term t) (Translation.term t))
  focusFree := Serial.focusFree_net (AtomEquality.Different.focusFree_sides _ _ _).1
    (Translation.allLabels_tensor _ (Translation.term_focusFree t) (Translation.term_focusFree t))
  holeFree := Serial.holeFree_net (AtomEquality.Different.holeFree_sides _ _ _).1
    (Translation.allLabels_tensor _ (Translation.term_holeFree t) (Translation.term_holeFree t))

/-- Arbitrary stored programs, including nested boxes and self-application, cannot introduce
another successful comparison cost. The conclusion includes all finite padding. -/
theorem shared_exact_cost (t : Term 0 0) (layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost (execution.initial ((sharedContents t).pad layers)) s ∧
      unboundedMachine.final s) ↔ cost = 7 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  have h := AtomEquality.Same.contents_exact_cost (Examples.binaryTree .atom) (Translation.term t) cost
  simpa only [serialLeft,AtomEquality.Same.inputPort,left_input,sharedContents,execution,Fin.val_zero,AtomEquality.Same.inputs,AtomEquality.Different.inputs,environmentInterface,
    List.replicate_zero,List.nil_append,List.length_cons,List.length_nil,Fin.zero_eta] using h

/-- Equal stored programs still give the distinct-store branch, at precisely seven steps,
under the full machine at every padded allowance. -/
theorem distinct_exact_cost (t : Term 0 0) (layers cost : Nat) :
    (∃ s, unboundedMachine.Steps cost (execution.initial ((distinctContents t).pad layers)) s ∧
      unboundedMachine.final s) ↔ cost = 7 := by
  rw [initial_cost_pad_iff,successful_unbounded_iff]
  have h := AtomEquality.Different.contents_exact_cost (ContractionTree.canonical .atom 1)
    (ContractionTree.canonical .atom 1) (Net.Tensor.net (Translation.term t) (Translation.term t)) cost
  simpa only [serialLeft,AtomEquality.Different.inputPort,left_input,distinctContents,execution,Fin.val_zero,AtomEquality.Same.inputs,AtomEquality.Different.inputs,environmentInterface,
    List.replicate_zero,List.nil_append,List.length_cons,List.length_nil,Fin.zero_eta] using h

/-- The shared-store Boolean is true for every translated content, not its evaluated value. -/
theorem shared_decision (t : Term 0 0) :
    AtomEquality.Decision (sharedContents t).graph (.input 0) true := by
  have h := AtomEquality.decision_map (MatchEmbedding.serialLeft _ (Translation.term t))
    (AtomEquality.Same.before_decision (Examples.binaryTree .atom) (Translation.depth t))
  simpa only [MatchEmbedding.serialLeft,AtomEquality.Same.inputPort,left_input,sharedContents,execution,Fin.val_zero,AtomEquality.Same.inputs,AtomEquality.Different.inputs,environmentInterface,
    List.replicate_zero,List.nil_append,List.length_cons,List.length_nil,Fin.zero_eta] using h

/-- The distinct-store Boolean is false even when the two stored translations are identical. -/
theorem distinct_decision (t : Term 0 0) :
    AtomEquality.Decision (distinctContents t).graph (.input 0) false := by
  have h := AtomEquality.decision_map
    (MatchEmbedding.serialLeft _ (Net.Tensor.net (Translation.term t) (Translation.term t)))
    (AtomEquality.Different.before_decision (ContractionTree.canonical .atom 1)
      (ContractionTree.canonical .atom 1) (Translation.depth t))
  simpa only [MatchEmbedding.serialLeft,AtomEquality.Different.inputPort,left_input,distinctContents,execution,Fin.val_zero,AtomEquality.Same.inputs,AtomEquality.Different.inputs,environmentInterface,
    List.replicate_zero,List.nil_append,List.length_cons,List.length_nil,Fin.zero_eta] using h

/-- The literal omega translation is retained as store data. Comparison terminates without
requiring a termination proof for that data; this theorem does not assert omega's divergence. -/
theorem omega_contents (layers cost : Nat) :
    ((∃ s, unboundedMachine.Steps cost
      (execution.initial ((sharedContents Hypernets.Copying.Examples.omegaTerm).pad layers)) s ∧ unboundedMachine.final s) ↔ cost = 7) ∧
    ((∃ s, unboundedMachine.Steps cost
      (execution.initial ((distinctContents Hypernets.Copying.Examples.omegaTerm).pad layers)) s ∧ unboundedMachine.final s) ↔ cost = 7) :=
  ⟨shared_exact_cost _ layers cost,distinct_exact_cost _ layers cost⟩
end Hypernets.Copying.EqualityCoherenceExamples
