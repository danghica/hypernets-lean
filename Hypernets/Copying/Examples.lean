import Hypernets.Copying.CanonicalTree
import Hypernets.Copying.Predicates
import Hypernets.Copying.Substitution

/-! Regression facts for the new representation. No observational equivalence
is asserted here: the concrete copying machine and template proofs are pending. -/
namespace Hypernets.Copying.Examples
open Graph

/-- Substituting an open term beneath a lambda does not capture its variable. -/
theorem substitution_avoids_capture :
    Term.instantiate (.lam (.app (.var 1) (.var 0)) : Term 3 0) (.var 1) =
      (.lam (.app (.var 2) (.var 0)) : Term 2 0) := rfl

/-- The external atom namespace is not shifted by a variable binder. -/
theorem atom_not_captured :
    Term.instantiate (.lam (.app (.var 1) (.atom 0))) (.atom 0) =
      (.lam (.app (.atom 0) (.atom 0)) : Term 0 1) := rfl

/-- Ordered source regression: the weakening is left of the first input. -/
theorem unary_tree_sources (s : ShareSort) :
    (CanonicalTree.net s 1).source 1 = [.internal 0, .input ⟨0,by simp⟩] := by
  cases s <;> rfl

/-- In the two-input tree the lower contraction has exactly the ordered inputs. -/
theorem binary_tree_sources (s : ShareSort) :
    (CanonicalTree.net s 2).source 2 = [.input ⟨0,by simp⟩, .input ⟨1,by simp⟩] := by
  cases s <;> rfl

/-- A canonical three-input tree has both weakening-to-root and spine adjacency. -/
theorem ternary_tree_adjacency (s : ShareSort) :
    (CanonicalTree.net s 3).Adjacent 0 1 ∧
    (CanonicalTree.net s 3).Adjacent 3 2 ∧
    (CanonicalTree.net s 3).Adjacent 2 1 ∧
    ¬ (CanonicalTree.net s 3).Adjacent 1 2 := by
  simp only [CanonicalTree.adjacent_iff]
  cases s <;> decide

/-- Boxing an instance preserves its free atom in the box's external interface. -/
def boxedInstance : Hypernet 1 [.thunk 0] [.atom] :=
  box (bound := 0) (freeVariables := 0) (freeAtoms := 1) (primitiveNet 0 .instanceEdge)

theorem boxedInstance_focusFree : FocusFree boxedInstance := by
  intro e f m
  intro h
  cases h

theorem boxedInstance_holeFree : HoleFree boxedInstance := by
  intro e f h
  intro eq
  cases eq

/-- Both terms in arbitrary named environments are weakenings of closed syntax.
This is a syntactic fact, not the semantic weakening law of Proposition 12.1. -/
theorem programs_in_environment {Name : Type} (E : Environment Name) :
    Term.rename Fin.elim0 Fin.elim0 (Term.privateCell 0 0) =
      Term.privateCell E.variables.length E.atoms.length ∧
    Term.rename Fin.elim0 Fin.elim0 (Term.constantResult 0 0) =
      Term.constantResult E.variables.length E.atoms.length :=
  ⟨Term.privateCell_rename _ _, Term.constantResult_rename _ _⟩

end Hypernets.Copying.Examples
