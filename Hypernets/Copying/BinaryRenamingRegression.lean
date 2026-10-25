import Hypernets.Copying.BoundaryPaddingRenaming

/-! Regression checks of actual nested and independently padded constructor graphs. -/
namespace Hypernets.Copying.ResourceAction
open Graph

theorem refl {d k h} (G : Hypernet d [.term] (environmentInterface k h)) :
    ResourceAction (Bijection.refl (Fin k)) (Bijection.refl (Fin h)) (BoundaryIso.refl G) :=
  ⟨fun _ => rfl,fun _ => rfl⟩
end Hypernets.Copying.ResourceAction

namespace Hypernets.Copying.Examples
open Graph

/-- Unequal allowances one and three, with nontrivial permutations of both resource sorts. -/
def unequalAllowanceRenaming :=
  Translation.padded_application_boundaryIso
    ((Translation.variableTerm_action 0 BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo 0).padTo 1 (by decide))
    ((Translation.atom_action 0 BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo 1).padTo 3 (by decide))

/-- The same construction is available for every binary operation. -/
def unequalAllowanceBinaryRenaming (o : Binary) :=
  Translation.padded_binary_boundaryIso
    ((Translation.variableTerm_action 0 BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo 0).padTo 1 (by decide))
    ((Translation.atom_action 0 BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo 1).padTo 3 (by decide)) o

/-- A genuine lambda-box operand at depth one may be composed with a depth-zero
constant when its own isomorphism is supplied. This is not a lambda-renaming proof. -/
def boxedOperandApplication (k h : Nat) :=
  Translation.padded_application_boundaryIso
    (Translation.constant_action 0 (Bijection.refl (Fin k)) (Bijection.refl (Fin h)) .unit)
    (ResourceAction.refl (Translation.term (.lam (.var 0) : Term k h)))

/-- Named distinct-list scopes use exactly the same original graph theorem. -/
theorem lambdaFree_namedEnvironment {Name : Type} (E : Environment Name)
    (t : Term E.variables.length E.atoms.length) (free : LambdaFree t)
    (ρ : Bijection (Fin E.variables.length) (Fin E.variables.length))
    (α : Bijection (Fin E.atoms.length) (Fin E.atoms.length)) :
    Nonempty (BoundaryIso (Translation.inEnvironment E t)
      (Translation.castDepth (Translation.depth_rename t ρ.toFun α.toFun)
        (Translation.inEnvironment E (Term.rename ρ.toFun α.toFun t)))) :=
  Translation.lambdaFree_rename t free ρ α
end Hypernets.Copying.Examples
