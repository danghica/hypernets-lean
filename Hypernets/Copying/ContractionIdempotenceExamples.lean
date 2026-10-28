import Hypernets.Copying.ContractionIdempotenceEquivalence
import Hypernets.Copying.NullaryBindingFree
import Hypernets.Copying.OperationalDeepExamples

/-! Non-vacuous Idem regressions: both sharing sorts occur in closed executable
contexts, and the literal pair remains below an actual copied lambda box. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionIdempotence.Examples
open Graph Combined

/-- Close either sharing sort by its original consuming primitives. -/
def finish (d : Nat) : (s : ShareSort) → Hypernet d [s.wire] []
  | .term => primitiveNet d (.operation (.const .unit))
  | .atom => Serial.net (primitiveNet d .store) (primitiveNet d (.operation (.const .unit)))

theorem finish_allLabels (P : Primitive → Prop) (d : Nat) (s : ShareSort)
    (store : P .store) (unit : P (.operation (.const .unit))) : AllLabels P (finish d s) := by
  cases s with
  | term => exact Translation.allLabels_primitive P d _ unit
  | atom =>
    exact Serial.allLabels_net P (Translation.allLabels_primitive P d _ store)
      (Translation.allLabels_primitive P d _ unit)

/-- An executable root is placed beside the literal nullary fragment and its
closing consumer. The fragment interface is genuinely empty. -/
def program {d : Nat} {s : ShareSort} (G : Hypernet d [] [s.wire]) : Hypernet d [.term] [] :=
  Net.Tensor.net (primitiveNet d (.operation (.const (.nat 7)))) (Serial.net G (finish d s))

/-- The two sides are genuinely different graph representations: the left
contains a contraction and the right contains only a weakening. -/
theorem left_not_iso (d : Nat) (s : ShareSort) : ¬ Nonempty (DeepIso (left d s) (right d s)) := by
  cases d <;> rintro ⟨f⟩
  all_goals
    have label := (Search.primitive_equiv (f.edge_label ⟨true,(0 : Fin 1)⟩) (.contraction s)).mp rfl
    have other : (right _ s).edgeLabel (f.edges.toFun ⟨true,(0 : Fin 1)⟩) = primitiveLabel _ (.weakening s) := rfl
    have bad := primitiveLabel_injective _ (other.symm.trans label)
    cases bad

/-- Both term and atom instances are present in an actual original recursive
specimen; this is not a relation between impossible open-program interfaces. -/
noncomputable def programWitness (d : Nat) (s : ShareSort) :
    FillingWitness template (program (left d s)) (program (right d s)) :=
  (FillingWitness.refl (primitiveNet d (.operation (.const (.nat 7))))
    (Translation.allLabels_primitive _ d _ (by intro m eq; cases eq))).tensor
    ((FillingWitness.of_rel 0 (literal d s)).serial
      (FillingWitness.refl (finish d s) (finish_allLabels _ d s
        (by intro m eq; cases eq) (by intro m eq; cases eq))))

theorem program_holeFree {d : Nat} {s : ShareSort} (G : Hypernet d [] [s.wire]) (closed : HoleFree G) :
    HoleFree (program G) :=
  Translation.allLabels_tensor _
    (Translation.allLabels_primitive _ d _ (by intro h eq; cases eq))
    (Serial.allLabels_net _ closed (finish_allLabels _ d s
      (by intro h eq; cases eq) (by intro h eq; cases eq)))

/-- The actual common context of each closed regression satisfies binding
freedom by nullarity, without choosing binding freedom as the observation class. -/
theorem program_bindingFree (d : Nat) (s : ShareSort) : BindingFree (programWitness d s).context :=
  (programWitness d s).nullary_bindingFree template_noInputs
    (program_holeFree _ (Step.holeFree (.idem d s)).1)

/-- The surrounding root executes one original search transition for either
literal side and either sharing sort, without traversing the nullary fragment. -/
theorem program_returns {d : Nat} {s : ShareSort} (G : Hypernet d [] [s.wire]) :
    Search.Step (program G) (.search,.input 0) (.backtrack,.input 0) := by
  cases d <;> apply Search.Step.search (G := program G) ⟨false,(0 : Fin 1)⟩ (.operation (.const (.nat 7))) _ _ rfl
  all_goals first | (change _ ∈ [_]; exact List.mem_cons_self) | rfl

/-- All successful finite runs of each actual closed regression have exactly
one transition, including every alternative contextual rewrite presentation. -/
theorem program_exact_cost {d : Nat} {s : ShareSort} (G : Hypernet d [] [s.wire]) (cost : Nat) :
    TerminatesIn cost ⟨program G,(.search,.input 0)⟩ ↔ cost = 1 := by
  rw [search_cost_iff (program_returns G)]
  simp only [final_cost_iff (show (machine d [.term] []).final
    ⟨program G,(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨n,hn,rfl⟩; omega
  · rintro rfl; exact ⟨0,rfl,rfl⟩

/-- The full proved template semantics applies to both concrete closed
instances and preserves all successful transition counts. -/
theorem program_exact_equiv (d : Nat) (s : ShareSort) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,program (left d s),(.search,.input 0)⟩
      ⟨d,program (right d s),(.search,.input 0)⟩ :=
  filling_exact_equiv (programWitness d s)
    (program_holeFree _ (Step.holeFree (.idem d s)).1)
    (program_holeFree _ (Step.holeFree (.idem d s)).2)

/-- A genuine boxed body retains the literal Idem pair, together with an
unused bound output, ready for the unchanged lambda-copying rule. -/
noncomputable def bodyWitness (d : Nat) (s : ShareSort) :=
  OperationalDeep.Examples.unusedWitness (programWitness d s)

/-- The paired copy results contain the original Idem occurrence in both
actual residual lambda bodies, with the original output distributors intact. -/
noncomputable def copiedBodyWitness (d : Nat) (s : ShareSort) :=
  (bodyWitness d s).deepCopy (Copying.Examples.binaryTree .term)

/-- Both actual original copy steps duplicate the lambda whose body contains
the term- or atom-Idem occurrence; no body evaluation is assumed. -/
theorem body_copy_steps (d : Nat) (s : ShareSort) :
    Combined.Step
      ⟨CopyRule.before (Copying.Examples.binaryTree .term)
        (lambdaPayload (OperationalDeep.Examples.unusedBody (program (left d s)))),
        (.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after (Copying.Examples.binaryTree .term)
        (lambdaPayload (OperationalDeep.Examples.unusedBody (program (left d s)))),
        (.search,.input ⟨0,by simp⟩)⟩ ∧
    Combined.Step
      ⟨CopyRule.before (Copying.Examples.binaryTree .term)
        (lambdaPayload (OperationalDeep.Examples.unusedBody (program (right d s)))),
        (.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after (Copying.Examples.binaryTree .term)
        (lambdaPayload (OperationalDeep.Examples.unusedBody (program (right d s)))),
        (.search,.input ⟨0,by simp⟩)⟩ :=
  ⟨Combined.local_step (.copy _ _ (.lambda _)),Combined.local_step (.copy _ _ (.lambda _))⟩

end Hypernets.Copying.ContractionIdempotence.Examples
