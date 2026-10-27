import Hypernets.Copying.BoxPermutationOpening
import Hypernets.Copying.ContextualRobustnessExamples

/-! Nontrivial swaps of both free resource sorts, a retained nested lambda,
and exact machine costs. These are instances of the unchanged translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.Opening.Examples
open Graph

def swap : TypedPermutation (environmentInterface 2 2) :=
  TypedPermutation.environment BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo

/-- The body itself contains a further lambda, an application, and an atom use. -/
def nestedBody : Hypernet 1 [.term] (environmentInterface 3 2) :=
  Translation.term (Term.lam (k := 3) (h := 2) (.app (.var 2) (.atom 0)))

def argument : Hypernet 2 [.term] [] := primitiveNet 2 (.operation (.const .unit))

theorem swaps_variable : swap.bijection.toFun (EnvironmentPermutation.termIndex (h := 2) 0) =
    EnvironmentPermutation.termIndex (h := 2) 1 := by
  rw [swap,TypedPermutation.environment_term]; rfl

theorem swaps_atom : swap.bijection.toFun (EnvironmentPermutation.atomIndex (k := 2) 0) =
    EnvironmentPermutation.atomIndex (k := 2) 1 := by
  rw [swap,TypedPermutation.environment_atom]; rfl

/-- Both free sorts move, but the bound argument position stays zero. -/
theorem fixes_bound : (bodyPermutation swap).bijection.toFun (0 : Fin 5) = (0 : Fin 5) := by
  apply Fin.ext
  rw [bodyPermutation,TypedPermutation.cast_val]
  rfl

/-- Even with the nested box present, the compensated side opens in exactly six steps. -/
theorem nested_opening :
    (Combined.machine 2 [.term] (environmentInterface 2 2 ++ [])).Steps 6
      (InterfacePermutation.state (swap.append (.refl [])).symm
        ⟨Application.before (InterfacePermutation.net nestedBody (bodyPermutation swap)) argument,(.search,.input 0)⟩)
      (InterfacePermutation.state (swap.append (.refl [])).symm
        ⟨Application.after (InterfacePermutation.net nestedBody (bodyPermutation swap)) argument,(.search,.input 0)⟩) :=
  (permuted_opening nestedBody argument (Stable.constant 2 .unit) swap).2.2.1

/-- Every successful continuation has the same exact cost on the two opened graphs. -/
theorem nested_successor_costs (n : Nat) :
    Combined.TerminatesIn n ⟨Application.after nestedBody argument,(.search,.input 0)⟩ ↔
    Combined.TerminatesIn n (InterfacePermutation.state (swap.append (.refl [])).symm
      ⟨Application.after (InterfacePermutation.net nestedBody (bodyPermutation swap)) argument,(.search,.input 0)⟩) :=
  successor_costs _ swap argument (permuted_action nestedBody swap) n

/-- The original stable argument edge is still present under the comparison. -/
theorem argument_retained :
    (afterCompensated (InterfacePermutation.iso nestedBody (bodyPermutation swap)) swap argument
      (permuted_action nestedBody swap)).edges.toFun (Application.argumentEdge nestedBody argument (0 : Fin 1)) =
    Application.argumentEdge (InterfacePermutation.net nestedBody (bodyPermutation swap)) argument (0 : Fin 1) :=
  argument_edge _ swap argument (permuted_action nestedBody swap) _
end Hypernets.Copying.BoxPermutation.Opening.Examples
