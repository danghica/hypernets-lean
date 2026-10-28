import Hypernets.Copying.BindingFillingWitness
import Hypernets.Copying.OperationalInputSafetyExamples

/-! Regression certificates with genuine operational occurrences below lambda
boxes, including a second nested box and both residual copies. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalDeep.Examples
open Graph Combined OperationalTemplates

/-- Expose an unused bound output with the original weakening edge. -/
def unusedBody {d} (G : Hypernet d [.term] []) :
    Hypernet d [.term] (environmentInterface 1 0) :=
  Net.Tensor.net G (primitiveNet d (.weakening .term))

def unusedWitness {T d} {G H : Hypernet d [.term] []} (w : FillingWitness T G H) :
    FillingWitness T (unusedBody G) (unusedBody H) :=
  w.tensor (FillingWitness.refl (primitiveNet d (.weakening .term))
    (by intro e; cases d <;> intro m eq <;> cases eq))

theorem unused_binding {T d} {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) : BindingFree (unusedWitness w).context := by
  apply w.tensor_binding _ binding
  exact BindingFree.of_holeFree _
    (by intro e; cases d <;> intro m eq <;> cases eq)
    (by intro e; cases d <;> intro h eq <;> cases eq)

noncomputable def referenceWitness (n : Nat) :=
  unusedWitness (FillingWitness.of_rel (T := template .referenceCreation) 0 (OperationalSafety.Examples.referencePair n))

theorem reference_binding (n : Nat) : BindingFree (referenceWitness n).context :=
  unused_binding _ (FillingWitness.of_rel_binding _ _)

/-- Copying a lambda duplicates the reference-creation occurrence in both
original residual branches; its store is not evaluated while copying. -/
theorem reference_copy_binding (n : Nat) :
    BindingFree ((referenceWitness n).deepCopy (Copying.Examples.binaryTree .term)).context :=
  (referenceWitness n).deepCopy_binding _ (reference_binding n)

/-- The certificate applies to the actual machine successors on both sides. -/
theorem reference_copy_steps (n : Nat) :
    Combined.Step
      ⟨CopyRule.before (Copying.Examples.binaryTree .term)
        (lambdaPayload (unusedBody (Allocation.before (Allocation.constantArgument n)))),
        (.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after (Copying.Examples.binaryTree .term)
        (lambdaPayload (unusedBody (Allocation.before (Allocation.constantArgument n)))),
        (.search,.input ⟨0,by simp⟩)⟩ ∧
    Combined.Step
      ⟨CopyRule.before (Copying.Examples.binaryTree .term)
        (lambdaPayload (unusedBody (Allocation.after (Allocation.constantArgument n)))),
        (.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after (Copying.Examples.binaryTree .term)
        (lambdaPayload (unusedBody (Allocation.after (Allocation.constantArgument n)))),
        (.search,.input ⟨0,by simp⟩)⟩ :=
  ⟨Combined.local_step (.copy _ _ (.lambda _)),Combined.local_step (.copy _ _ (.lambda _))⟩

noncomputable def betaWitness (n : Nat) :=
  unusedWitness (FillingWitness.of_rel (T := template .microBeta) 1 (OperationalSafety.Examples.betaPair n))

theorem beta_binding (n : Nat) : BindingFree (betaWitness n).context :=
  unused_binding _ (FillingWitness.of_rel_binding _ _)

/-- The unchanged variable-body beta occurrence can likewise be duplicated. -/
theorem beta_copy_binding (n : Nat) :
    BindingFree ((betaWitness n).deepCopy (Copying.Examples.binaryTree .term)).context :=
  (betaWitness n).deepCopy_binding _ (beta_binding n)

/-- A second enclosing lambda preserves the actual nested certificate. -/
noncomputable def nestedReferenceWitness (n : Nat) :=
  unusedWitness (referenceWitness n).lambdaPayload

theorem nestedReference_binding (n : Nat) : BindingFree (nestedReferenceWitness n).context :=
  unused_binding _ ((referenceWitness n).lambdaPayload_binding (reference_binding n))

/-- Both copied branches retain two levels of original boxes and their store
rewrite occurrence, without any body-termination assumption. -/
theorem nestedReference_copy_binding (n : Nat) :
    BindingFree ((nestedReferenceWitness n).deepCopy (Copying.Examples.binaryTree .term)).context :=
  (nestedReferenceWitness n).deepCopy_binding _ (nestedReference_binding n)

end Hypernets.Copying.OperationalDeep.Examples
