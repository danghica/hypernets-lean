import Hypernets.Copying.PropositionAllocationEquivalence
import Hypernets.Copying.PaddedContextCongruence

/-! Lift the genuine reference-creation and micro-beta pairs and their actual
binding-free graph contexts. No padding invariance follows from determinism. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2
open Graph

/-- Each extra allowance uses the proved operational-template closure law. -/
theorem operational_pair_pad {kind d I O} {G H : Hypernet d I O}
    (pair : OperationalTemplates.Pair kind G H) (n : Nat) :
    OperationalTemplates.Pair kind (Translation.pad d n G) (Translation.pad d n H) := by
  induction n with
  | zero => exact pair
  | succ n ih => exact ih.raise

/-- Lift a contextual use of a template only after proving the fragment
comparison at every padded allowance. The certified context itself is padded. -/
theorem context_equiv_pad {r v a d k h} (C : GraphContext r v a d k h)
    (G H : OpenProgram r v a) (L R : OpenProgram d k h)
    (rel : ∀ n, Combined.execution.Equiv CostOrder.any (G.pad n) (H.pad n))
    (left : DeepIso (C.fill G).graph L.graph) (right : DeepIso (C.fill H).graph R.graph)
    (n : Nat) : Combined.execution.Equiv CostOrder.any (L.pad n) (R.pad n) := by
  have middle := Combined.execution.equiv_context_padded Combined.execution_respectsIso C rel n
  have l := Combined.execution.equiv_iso Combined.execution_respectsIso ((C.fill G).pad n) (L.pad n) (Padding.pad_congr left n)
  have r := Combined.execution.equiv_iso Combined.execution_respectsIso ((C.fill H).pad n) (R.pad n) (Padding.pad_congr right n)
  exact Combined.execution.equiv_trans ⟨l.2,l.1⟩ (Combined.execution.equiv_trans middle r)

/-- Allocation at arbitrary allowance retains the original translated closure. -/
theorem original_allocated_pad (n : Nat) : Combined.execution.Equiv CostOrder.any
    (originalProgram.pad n) (allocatedProgram.pad n) :=
  context_equiv_pad (applicationContext (Application.closure body) closure_focusFree closure_holeFree)
    referenceSource referenceTarget originalProgram allocatedProgram
    (fun n => OperationalTemplates.pair_contextual_equiv _ _ (operational_pair_pad referencePair n))
    ((applicationContext_fill _ _ _ _).trans source_iso.symm)
    (applicationContext_fill _ _ _ _) n

/-- The private store stays outside the stable argument at every allowance. -/
theorem betaSource_opened_pad (n : Nat) : Combined.execution.Equiv CostOrder.any
    (betaSourceProgram.pad n) (openedProgram.pad n) :=
  context_equiv_pad (storeContext (storeSuffix 3) (storeSuffix_focusFree 3) (storeSuffix_holeFree 3))
    betaLeft betaRight betaSourceProgram openedProgram
    (fun n => OperationalTemplates.pair_contextual_equiv _ _ (operational_pair_pad betaPair n))
    (storeContext_fill _ _ _ _) (storeContext_fill _ _ _ _) n

/-- The complete actual allocation/beta prefix at every extra allowance. -/
theorem original_opened_pad (n : Nat) : Combined.execution.Equiv CostOrder.any
    (originalProgram.pad n) (openedProgram.pad n) :=
  Combined.execution.equiv_trans (original_allocated_pad n)
    (Combined.execution.equiv_trans
      (Combined.execution.equiv_iso Combined.execution_respectsIso (allocatedProgram.pad n) (betaSourceProgram.pad n) (Padding.pad_congr allocated_iso n))
      (betaSource_opened_pad n))

/-- A caller may choose any common allowance at least three. -/
theorem original_opened_padTo (N : Nat) (bound : 3 ≤ N) : Combined.execution.Equiv CostOrder.any
    (originalProgram.padTo N bound) (openedProgram.padTo N bound) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [OpenProgram.padTo_add,OpenProgram.padTo_add]
  exact original_opened_pad n

end Hypernets.Copying.Proposition12_2
