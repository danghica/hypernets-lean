import Hypernets.Copying.TranslationClauses

namespace Hypernets.Copying.Examples
open Graph

/-- The unchanged `ref 1` subterm, using the paper's constant and unary clauses. -/
def referenceOne (k h : Nat) : Hypernet 0 [.term] (environmentInterface k h) :=
  Translation.unary .ref (Translation.constant 0 k h (.nat 1))

theorem referenceOne_language (k h : Nat) : Translation.LanguageGraph (referenceOne k h) :=
  Translation.unary_language _ (Translation.constant_language _ _ _ _)

/-- Unused environments remain explicit: one constant and three weakening edges. -/
theorem constant_environment_edges :
    (Translation.constant 0 2 1 (.nat 1)).finiteEdge.elements.length = 4 := by decide

/-- The selected variable keeps its weakening/contraction pair, plus all unused resources. -/
theorem variable_environment_edges :
    (Translation.variableTerm 0 2 (1 : Fin 3)).finiteEdge.elements.length = 6 := by decide

/-- Atom translation includes the instance edge as well as its sharing pair. -/
theorem atom_environment_edges :
    (Translation.atom 0 3 (1 : Fin 2)).finiteEdge.elements.length = 7 := by decide

/-- A unary clause adds six distributor edges for the three ambient resources. -/
theorem referenceOne_environment_edges :
    (referenceOne 2 1).finiteEdge.elements.length = 11 := by decide

/-- A bound occurrence remains the first output of the boxed body. -/
def identityAbstraction : Hypernet 1 [.term] (environmentInterface 0 0) :=
  Translation.abstraction (Translation.variableTerm 0 0 (0 : Fin 1))

theorem identityAbstraction_language : Translation.LanguageGraph identityAbstraction :=
  Translation.abstraction_language (Translation.variable_language _ _ _)

/-- Lambda translation has a lambda edge and a real box, even with no free environment. -/
theorem identityAbstraction_outer_edges : identityAbstraction.finiteEdge.elements.length = 2 := by decide

/-- The term and atom single-use distributors contain two edges per resource. -/
theorem singleUse_retains_edges :
    (Translation.singleUse 0 2 1).finiteEdge.elements.length = 6 := by decide

end Hypernets.Copying.Examples
