import Hypernets.Copying.BoxPermutationInvariants

/-! Regression statements cover nested binders, unequal allowances, both resource
sorts, named scopes, and the two unchanged Proposition 12.2 programs. -/
namespace Hypernets.Copying.Examples
open Graph EnvironmentPermutation BoxPermutation

/-- Every original term admits a finite derivation to its boundary-compensated renaming. -/
theorem termRenamingDerivation {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    ∃ eq : Translation.depth (Term.rename ρ.toFun α.toFun t) = Translation.depth t,
      Derivation (Translation.term t)
        (InterfacePermutation.net (Translation.castDepth eq (Translation.term (Term.rename ρ.toFun α.toFun t)))
          (TypedPermutation.environment ρ α).symm) :=
  (Translation.term_rename_via_boxPermutation t ρ α).derivation

/-- This uses the actual original let/ref/sequence encoding, including every nested lambda. -/
theorem privateCell_fullRenaming {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Renaming ρ α (Translation.privateCell k h)
      (Translation.term (Term.rename ρ.toFun α.toFun (Term.privateCell k h))) :=
  Translation.term_rename_via_boxPermutation _ ρ α

theorem constantResult_fullRenaming {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Renaming ρ α (Translation.constantResult k h)
      (Translation.term (Term.rename ρ.toFun α.toFun (Term.constantResult k h))) :=
  Translation.term_rename_via_boxPermutation _ ρ α

/-- Two lambda levels above an application retain the outer free variable and atom. -/
def nestedRenamingTerm : Term 2 2 := .lam (.lam (.app (.var 2) (.atom 0)))

theorem nestedRenaming : Renaming BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo
    (Translation.term nestedRenamingTerm)
    (Translation.term (Term.rename BoundaryRenamingExamples.swapTwo.toFun BoundaryRenamingExamples.swapTwo.toFun nestedRenamingTerm)) :=
  Translation.term_rename_via_boxPermutation _ _ _

/-- The original maximum allowance is exercised by a constant beside a nested box. -/
theorem unequalDepthRenaming : Renaming BoundaryRenamingExamples.swapTwo BoundaryRenamingExamples.swapTwo
    (Translation.term (.app (.const .unit) nestedRenamingTerm))
    (Translation.term (Term.rename BoundaryRenamingExamples.swapTwo.toFun BoundaryRenamingExamples.swapTwo.toFun
      (.app (.const .unit) nestedRenamingTerm))) :=
  Translation.term_rename_via_boxPermutation _ _ _

/-- The theorem boundary supports every distinct-list environment, not just closed terms. -/
theorem full_namedEnvironment {Name : Type} (E : Environment Name)
    (t : Term E.variables.length E.atoms.length)
    (ρ : Bijection (Fin E.variables.length) (Fin E.variables.length))
    (α : Bijection (Fin E.atoms.length) (Fin E.atoms.length)) :
    Renaming ρ α (Translation.inEnvironment E t)
      (Translation.inEnvironment E (Term.rename ρ.toFun α.toFun t)) :=
  Translation.term_rename_via_boxPermutation t ρ α

/-- The bound prefix is not a freely permutable resource block. -/
theorem captured_swap_rejected :
    ¬ ∃ p : Pair 1 1 0, ∀ i,
      p.body.bijection.toFun (termIndex (h := 0) i) =
        termIndex (BoundaryRenamingExamples.swapTwo.toFun i) := by
  rintro ⟨p,eq⟩
  have a := p.bound (0 : Fin 1)
  have b := eq (0 : Fin 2)
  have same : boundIndex (k := 1) (h := 0) (0 : Fin 1) = termIndex (h := 0) (0 : Fin 2) := rfl
  rw [same] at a
  have bad := congrArg Fin.val (a.symm.trans b)
  contradiction

/-- Even with two well-typed boxes, their ordered isomorphism cannot implement this swap. -/
theorem box_swap_not_iso {d} (G H : Hypernet d [.term] (environmentInterface 3 0)) :
    ¬ ∃ f : BoundaryIso (box (bound := 1) (freeVariables := 2) G)
        (box (bound := 1) (freeVariables := 2) H),
      ∀ i, f.ports.toFun (.output i) = .output
        ((TypedPermutation.environment BoundaryRenamingExamples.swapTwo (Bijection.refl (Fin 0))).bijection.toFun i) := by
  apply nontrivial_not_ordered
  refine ⟨termIndex (h := 0) (0 : Fin 2),?_⟩
  rw [TypedPermutation.environment_term]
  intro eq
  have bad := congrArg Fin.val eq
  contradiction
/-- The printed unshifted free-position equation in Definition 12.7(2)
is already inconsistent at one bound and one free variable. The formal pair
uses the bound-prefix offset explicitly. This does not change the translation. -/
theorem unshifted_box_pair_impossible (body : Bijection (Fin 2) (Fin 2))
    (free : Bijection (Fin 1) (Fin 1)) :
    ¬ (body.toFun 0 = 0 ∧ (body.toFun 1).val = (free.toFun 0).val) := by
  rintro ⟨bound,unshifted⟩
  have freeZero : (free.toFun 0).val = 0 := by have := (free.toFun 0).isLt; omega
  have collision : body.toFun 1 = body.toFun 0 := Fin.ext (by rw [bound]; simp only [Fin.val_zero]; omega)
  have bad := congrArg Fin.val (body.injective collision)
  contradiction
end Hypernets.Copying.Examples
