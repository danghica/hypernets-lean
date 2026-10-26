import Hypernets.Copying.CombinedPaddingInvariant
import Hypernets.Copying.ArithmeticExamples

/-! Regression checks for depth-zero obstructions, nested boxes, untouched
Proposition 12.2 programs, and arbitrary contextual observations. -/
namespace Hypernets.Copying.Lowering.Examples
open Graph

/-- A real lambda box cannot be mistaken for unused representation allowance. -/
theorem lambda_needs_layer {k h} (B : Hypernet 0 [.term] (environmentInterface (k+1) h)) :
    ¬ Fits (Copying.lambdaPayload B) := Copyable.lambda_not_fits B

/-- Arbitrary nested lambda bodies remain copyable after every padding and lowering. -/
theorem nested_payload_copyable {d k h}
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (layers : Nat) :
    Copyable (Translation.pad (d+1) layers (Copying.lambdaPayload B)) :=
  (Copyable.pad_iff _ layers).mpr (.lambda B)

/-- An excessive box used only as an erased slot imposes no restriction on the filler. -/
theorem erased_box_slot_fits {bound k h}
    (B : Hypernet 0 [.term] (environmentInterface (bound+k) h))
    (G : Hypernet 1 [.thunk bound] (environmentInterface k h)) (fit : Fits G) :
    Fits ((Copying.box B).plug (0 : Fin 1) G) ∧ ¬ Fits (Copying.box B) := by
  refine ⟨(fits_plug _ _ _).mpr ⟨?_,fit⟩,box_not_fits B⟩
  intro b ne
  exact False.elim (ne (Fin.ext (by have := b.isLt; omega)))

/-- Neither auxiliary lowering nor its proof introduces a hole into a translated program. -/
theorem translated_roundtrip_language {k h} (t : Term k h) :
    Translation.LanguageGraph (graph (Padding.graph (Translation.term t))) := by
  apply (allLabels_iff _ _ (fits_graph _)).mpr
  rw [Padding.graph_eq_raise]
  exact (allLabels_raise_iff _ _ _).mpr (Translation.term_language t)

/-- Every observation of the literal private-cell program retains all successful costs,
for arbitrary variable/atom environments and every certified closing context. -/
theorem privateCell_observation_padding {k h} (C : ClosingContext 3 k h) (layers : Nat) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      (Combined.execution.initial (C.close (translatedProgram (Term.privateCell k h) 3 (by change 3 ≤ 3; decide))))
      (Combined.execution.initial ((C.pad layers).close
        ((translatedProgram (Term.privateCell k h) 3 (by change 3 ≤ 3; decide)).pad layers))) :=
  Combined.close_pad_equiv CostOrder.exact C _ layers

/-- The unchanged constant-result program has the same representation guarantee. -/
theorem constantResult_observation_padding {k h} (C : ClosingContext 2 k h) (layers : Nat) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      (Combined.execution.initial (C.close (translatedProgram (Term.constantResult k h) 2 (by change 2 ≤ 2; decide))))
      (Combined.execution.initial ((C.pad layers).close
        ((translatedProgram (Term.constantResult k h) 2 (by change 2 ≤ 2; decide)).pad layers))) :=
  Combined.close_pad_equiv CostOrder.exact C _ layers

/-- Nontermination cannot be repaired by extra allowance, including in contexts
with nonterminating callbacks or repeated uses of a captured closure. This is
an invariance theorem, not a classification of those contexts' behaviour. -/
theorem nontermination_padding {d k h} (C : ClosingContext d k h)
    (G : OpenProgram d k h) (layers : Nat) :
    (¬ Combined.execution.Terminates ((C.close G).pad layers)) ↔
      ¬ Combined.execution.Terminates (C.close G) :=
  not_congr (Combined.terminates_pad_iff (C.close G) layers)

end Hypernets.Copying.Lowering.Examples
