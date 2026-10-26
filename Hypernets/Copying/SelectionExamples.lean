import Hypernets.Copying.CombinedSafety

/-! Regression consequences for ordered arithmetic, actual stores, embedded values,
and arbitrary observations of the unchanged Proposition 12.2 terms. -/
namespace Hypernets.Copying.SelectionExamples
open Graph

/-- Reversing unequal natural operands cannot describe a second match at the same token. -/
theorem unequal_operands_not_swappable {d r s I O} {G : Hypernet d I O}
    (o : Arithmetic.BinaryCode) (m n : Nat) (different : m ≠ n)
    (f : MatchEmbedding (Arithmetic.binaryBefore o r m n) G)
    (g : MatchEmbedding (Arithmetic.binaryBefore o s n m) G) :
    f.ports (.input 0) ≠ g.ports (.input 0) := by
  intro same
  exact different (Arithmetic.binary_match_unique f g same).2.1

/-- The runtime alphabet genuinely needs the store introduced by reference allocation. -/
theorem allocation_not_translation_alphabet {d O} (G : Hypernet d [.term] O) :
    ¬ Translation.LanguageGraph (Allocation.after G) := by
  intro h
  have bad := h (Allocation.store G)
  rw [Allocation.store_label] at bad
  exact (Dereference.label_primitive _ _ _).mp bad

/-- Allocation remains safe in the runtime alphabet despite leaving the translation alphabet. -/
theorem allocation_runtime (d n : Nat) : RuleSafety.RuntimeGraph (Allocation.after (Arithmetic.number d n)) := by
  apply Combined.rewrite_runtime (.local (.allocate _ (Stable.constant d (.nat n))))
  apply RuleSafety.language_runtime
  exact Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial)
    (Translation.allLabels_primitive _ _ _ trivial)

/-- An already evaluated numeric argument cannot become a rewrite request after context attachment. -/
theorem embedded_number_no_rewrite {d r I O} {G H : Hypernet d I O} (n : Nat)
    (f : MatchEmbedding (Arithmetic.number r n) G) {w} :
    ¬ Combined.Rewrite G (f.ports (.input 0)) H w :=
  Combined.stable_occurrence_no_rewrite (Stable.constant r (.nat n)) f

/-- Every finite run in any certified closing context of the literal private-cell term is safe.
This includes finite prefixes of divergent callbacks; no termination assertion is made. -/
theorem privateCell_runs_safe {k h} (C : ClosingContext 3 k h) {n t}
    (run : Combined.unboundedMachine.Steps n
      (Combined.execution.initial (C.close (translatedProgram (Term.privateCell k h) 3 (by change 3 ≤ 3; decide)))) t) :
    FocusFree t.2.1 ∧ HoleFree t.2.1 := Combined.reachable_safe _ run

/-- The same all-context, all-prefix invariant holds for the unchanged constant-result term. -/
theorem constantResult_runs_safe {k h} (C : ClosingContext 2 k h) {n t}
    (run : Combined.unboundedMachine.Steps n
      (Combined.execution.initial (C.close (translatedProgram (Term.constantResult k h) 2 (by change 2 ≤ 2; decide)))) t) :
    FocusFree t.2.1 ∧ HoleFree t.2.1 := Combined.reachable_safe _ run
end Hypernets.Copying.SelectionExamples
