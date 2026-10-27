import Hypernets.Copying.SemanticRenaming
import Hypernets.Copying.FullRenamingExamples

/-! Semantic regressions for compensated full-syntax renaming. The two original
Proposition 12.2 terms are tested independently: no equivalence between them is
asserted by these renaming results. -/
namespace Hypernets.Copying.Examples
open Graph

/-- Two nested binders preserve the observable behaviour of simultaneous
variable and atom swaps, after restoring their original external connections. -/
theorem nestedRenaming_contextual_exact :
    Combined.execution.Equiv CostOrder.exact
      (translatedProgram nestedRenamingTerm 2 (by decide))
      (renamedProgram nestedRenamingTerm BoundaryRenamingExamples.swapTwo
        BoundaryRenamingExamples.swapTwo 2 (by decide)) :=
  Translation.term_rename_contextual_exact _ _ _ _ _

/-- An application with branch allowances zero and two is tested at allowance
three, exercising both the original maximum padding and extra outer padding. -/
theorem unequalDepthRenaming_contextual_exact :
    Combined.execution.Equiv CostOrder.exact
      (translatedProgram (.app (.const .unit) nestedRenamingTerm) 3 (by decide))
      (renamedProgram (.app (.const .unit) nestedRenamingTerm)
        BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo 3 (by decide)) :=
  Translation.term_rename_contextual_exact _ _ _ _ _

/-- Exact successful-run counts agree in every closing graph context; the
context's own nesting depth and effects are not bounded by this regression. -/
theorem unequalDepthRenaming_contextual_count (C : ClosingContext 3 2 2) (n : Nat) :
    (∃ a, Combined.unboundedMachine.Steps n
      (Combined.execution.initial
        (C.close (translatedProgram (.app (.const .unit) nestedRenamingTerm) 3 (by decide)))) a ∧
          Combined.unboundedMachine.final a) ↔
    (∃ b, Combined.unboundedMachine.Steps n
      (Combined.execution.initial
        (C.close (renamedProgram (.app (.const .unit) nestedRenamingTerm)
          BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo 3 (by decide)))) b ∧
          Combined.unboundedMachine.final b) :=
  Translation.term_rename_contextual_count _ _ _ _ _ C n

/-- The original let/ref/lambda/sequence/dereference term is independent of its
ambient resource names. This is a renaming theorem for the left term alone. -/
theorem privateCell_contextualRenaming {k h}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (d : Nat) (bound : Translation.depth (Term.privateCell k h) ≤ d) :
    Combined.execution.Equiv CostOrder.exact
      (translatedProgram (Term.privateCell k h) d bound)
      ((translatedProgram (Term.privateCell k h) d bound).permute
        (TypedPermutation.environment ρ α).symm) :=
  Translation.term_rename_contextual_exact (Term.privateCell k h) ρ α d bound

/-- The original lambda/sequence/constant term has the corresponding independent
renaming result, at every variable/atom scope and sufficient allowance. -/
theorem constantResult_contextualRenaming {k h}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (d : Nat) (bound : Translation.depth (Term.constantResult k h) ≤ d) :
    Combined.execution.Equiv CostOrder.exact
      (translatedProgram (Term.constantResult k h) d bound)
      ((translatedProgram (Term.constantResult k h) d bound).permute
        (TypedPermutation.environment ρ α).symm) :=
  Translation.term_rename_contextual_exact (Term.constantResult k h) ρ α d bound

/-- The semantic interface also accepts arbitrary named distinct-list scopes,
without assuming that either resource environment is empty. -/
theorem privateCell_named_contextualRenaming {Name : Type} (E : Environment Name)
    (ρ : Bijection (Fin E.variables.length) (Fin E.variables.length))
    (α : Bijection (Fin E.atoms.length) (Fin E.atoms.length))
    (d : Nat) (bound : Translation.depth (Term.privateCell E.variables.length E.atoms.length) ≤ d) :
    Combined.execution.Equiv CostOrder.exact
      (translatedProgram (Term.privateCell E.variables.length E.atoms.length) d bound)
      ((translatedProgram (Term.privateCell E.variables.length E.atoms.length) d bound).permute
        (TypedPermutation.environment ρ α).symm) :=
  privateCell_contextualRenaming ρ α d bound

end Hypernets.Copying.Examples
