import Hypernets.Copying.LambdaFreeRenaming

/-! Concrete original-language instances and a rejected operand-action mismatch. -/
namespace Hypernets.Copying.Examples
open Graph EnvironmentPermutation

/-- The callback invocation appearing inside both programs of Proposition 12.2. -/
theorem callbackInvocation_rename {k h} (i : Fin k)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (Translation.term (.app (.var i) (.const .unit) : Term k h))
      (Translation.term (.app (.var (ρ.toFun i)) (.const .unit) : Term k h))) :=
  Translation.lambdaFree_rename _ (.application (.var i) (.constant .unit)) ρ α

/-- The two operand occurrences share the same resource, with both use blocks retained. -/
theorem repeatedVariable_rename {k h} (i : Fin k)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (Translation.term (.app (.var i) (.var i) : Term k h))
      (Translation.term (.app (.var (ρ.toFun i)) (.var (ρ.toFun i)) : Term k h))) :=
  Translation.lambdaFree_rename _ (.application (.var i) (.var i)) ρ α

/-- Assignment combines atom renaming and reference creation without simplifying either translation. -/
theorem assignmentAllocation_rename {k h} (a : Fin h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (Translation.term (.binary .assign (.atom a) (.unary .ref (.const (.nat 1))) : Term k h))
      (Translation.term (.binary .assign (.atom (α.toFun a)) (.unary .ref (.const (.nat 1))) : Term k h))) :=
  Translation.lambdaFree_rename _ (.binary .assign (.atom a) (.unary .ref (.constant (.nat 1)))) ρ α

/-- The same proof applies to addition, subtraction, assignment, and atom equality. -/
theorem everyBinary_rename {k h} (o : Binary) (i : Fin k) (a : Fin h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (Translation.term (.binary o (.unary .deref (.var i)) (.atom a) : Term k h))
      (Translation.term (.binary o (.unary .deref (.var (ρ.toFun i))) (.atom (α.toFun a)) : Term k h))) :=
  Translation.lambdaFree_rename _ (.binary o (.unary .deref (.var i)) (.atom a)) ρ α

/-- Nontrivial renaming of both resource sorts in one shared application graph. -/
def twoSortExample : Term 2 2 :=
  .app (.unary .deref (.var 0)) (.binary .atomEq (.atom 0) (.atom 1))

theorem twoSortExample_free : LambdaFree twoSortExample :=
  .application (.unary .deref (.var 0)) (.binary .atomEq (.atom 0) (.atom 1))

theorem twoSortExample_rename :
    Nonempty (BoundaryIso (Translation.term twoSortExample)
      (Translation.term (Term.rename BoundaryRenamingExamples.swapTwo.toFun BoundaryRenamingExamples.swapTwo.toFun twoSortExample))) :=
  Translation.lambdaFree_rename _ twoSortExample_free BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo

/-- Typed operand isomorphisms alone need not agree: swapping resources on one
side and fixing them on the other fails at the first variable output. -/
theorem mismatched_operand_actions :
    ¬ (∀ j, (Translation.constant_rename 0 BoundaryRenamingExamples.swapTwo (Bijection.refl (Fin 0)) .unit).outputs.toFun j =
      (Translation.constant_rename 0 (Bijection.refl (Fin 2)) (Bijection.refl (Fin 0)) .unit).outputs.toFun j) := by
  intro agree
  have lhs := (Translation.constant_action 0 BoundaryRenamingExamples.swapTwo (Bijection.refl (Fin 0)) .unit).term 0
  have rhs := (Translation.constant_action 0 (Bijection.refl (Fin 2)) (Bijection.refl (Fin 0)) .unit).term 0
  rw [BoundaryIso.map_output] at lhs rhs
  have eq := (Port.output.inj lhs).symm.trans ((agree (termIndex (h := 0) (0 : Fin 2))).trans (Port.output.inj rhs))
  have vals := congrArg (fun j : Fin (environmentInterface 2 0).length => j.val) eq
  contradiction
end Hypernets.Copying.Examples
