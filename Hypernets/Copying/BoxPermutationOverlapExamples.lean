import Hypernets.Copying.BoxPermutationOverlapCosts
import Hypernets.Copying.BoxPermutationOpeningExamples

/-! Nontrivial variable/atom permutations, both copy branches, and genuine
surrounding operations. The tests do not assume whole-template robustness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.OverlapExamples
open Graph Combined Opening.Examples

/-- A body with a nested lambda; both free variable and atom orders are swapped. -/
def changedBody := InterfacePermutation.net nestedBody (Opening.bodyPermutation swap)

/-- Every contraction-tree presentation, including unary trees, has the same
matched two-transition copying prefix and the checked residual derivation. -/
theorem nested_copying {n} (T : ContractionTree .term (n+1)) :
    (machine 2 (List.replicate (n+1) .term) (environmentInterface 2 2)).Steps 2
      (InterfacePermutation.state swap.symm
        ⟨CopyRule.before T (lambdaPayload changedBody),(.search,.input ⟨0,by simp⟩)⟩)
      (InterfacePermutation.state swap.symm
        ⟨CopyRule.after T (lambdaPayload changedBody),(.search,.input ⟨0,by simp⟩)⟩) ∧
    Derivation (CopyRule.after T (lambdaPayload nestedBody))
      (InterfacePermutation.net (CopyRule.after T (lambdaPayload changedBody)) swap.symm) :=
  (Copying.initial_diamond T _ swap (Opening.permuted_action nestedBody swap)).2

/-- The real binary tree is retained; the residual does not collapse the two boxes. -/
theorem binary_boxes :
    CopyRule.leftEdge (Hypernets.Copying.Examples.binaryTree .term) (lambdaPayload nestedBody)
      (Copying.boxEdge nestedBody) ≠
    CopyRule.rightEdge (Hypernets.Copying.Examples.binaryTree .term) (lambdaPayload nestedBody)
      (Copying.boxEdge nestedBody) := Copying.residual_boxes_distinct _ _

/-- The zero-residual-input case still uses the complete copying construction. -/
theorem unary_copying : Derivation
    (CopyRule.after (ContractionTree.canonical .term 1) (lambdaPayload nestedBody))
    (InterfacePermutation.net
      (CopyRule.after (ContractionTree.canonical .term 1) (lambdaPayload changedBody)) swap.symm) :=
  (nested_copying (ContractionTree.canonical .term 1)).2

/-- Free-output naturality keeps the active and unselected input positions fixed. -/
theorem third_input_fixed :
    (CopyRule.Boundary.after (ContractionTree.canonical .term 3)
      (InterfacePermutation.iso (lambdaPayload nestedBody) swap)).ports.toFun
        (.input (2 : Fin 3)) = .input (2 : Fin 3) :=
  CopyRule.Boundary.after_input _ _ _

/-- Full costs of the actual application sources, not only their successors. -/
theorem nested_redex_costs (cost : Nat) :
    TerminatesIn cost ⟨Application.before nestedBody argument,(.search,.input (0 : Fin 1))⟩ ↔
    TerminatesIn cost (InterfacePermutation.state (swap.append (.refl [])).symm
      ⟨Application.before changedBody argument,(.search,.input (0 : Fin 1))⟩) :=
  Opening.redex_costs _ swap argument (Stable.constant 2 .unit) (Opening.permuted_action nestedBody swap) cost

/-- Negation supplies a real enclosing operation, so the local input is internal
to the host and local return does not by itself imply global finality. -/
def host : Hypernet 2 [.term] (environmentInterface 2 2 ++ []) :=
  Serial.net (primitiveNet 2 (.operation (.unary .neg)))
    (primitiveNet 2 (.hole ⟨0,[.term],environmentInterface 2 2 ++ []⟩))

def hole : host.Edge := Serial.rightEdge _ _ (0 : Fin 1)

theorem hosted_redex_costs (cost : Nat) :
    TerminatesIn cost (plugState host hole
      ⟨Application.before nestedBody argument,(.search,.input (0 : Fin 1))⟩) ↔
    TerminatesIn cost (plugState host hole
      (InterfacePermutation.state (swap.append (.refl [])).symm
        ⟨Application.before changedBody argument,(.search,.input (0 : Fin 1))⟩)) :=
  Opening.redex_costs_at _ swap argument host hole rfl rfl (Stable.constant 2 .unit)
    (Opening.permuted_action nestedBody swap) cost

/-- The self-application body is copied with its boxes intact. This is a finite
prefix/structure regression, not an assertion that its evaluation terminates. -/
def selfApplication : Term 3 2 :=
  .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

theorem self_application_copying :
    Derivation (CopyRule.after (Hypernets.Copying.Examples.binaryTree .term)
      (lambdaPayload (Translation.term selfApplication)))
      (InterfacePermutation.net (CopyRule.after (Hypernets.Copying.Examples.binaryTree .term)
        (lambdaPayload (InterfacePermutation.net (Translation.term selfApplication)
          (Opening.bodyPermutation swap)))) swap.symm) :=
  (Copying.permuted_copying _ (Translation.term selfApplication) swap).2
end Hypernets.Copying.BoxPermutation.OverlapExamples
