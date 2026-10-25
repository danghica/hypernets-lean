import Hypernets.Copying.UnaryBoundaryRenaming
import Hypernets.Copying.TranslationExamples

/-! Renaming for arbitrarily many original unary operations over atomic terms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph

/-- An indexed subclass of the original syntax, not a replacement language. -/
inductive UnaryFragment {k h} : Term k h → Prop where
  | atomic {t} : Atomic t → UnaryFragment t
  | unary (o : Unary) {t} : UnaryFragment t → UnaryFragment (.unary o t)

/-- Equality transport of the allowance commutes with the unchanged unary clause. -/
theorem castDepth_unary {d n k h} (eq : d = n) (o : Unary)
    (G : Hypernet d [.term] (environmentInterface k h)) :
    castDepth eq (unary o G) = unary o (castDepth eq G) := by
  cases eq; rfl

/-- The entire unary fragment of Figure 16 respects bijective resource renaming,
with no operational, stability, or template hypotheses. -/
theorem unaryFragment_rename {k h} (t : Term k h) (fragment : UnaryFragment t)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (term t)
      (castDepth (depth_rename t ρ.toFun α.toFun) (term (Term.rename ρ.toFun α.toFun t)))) := by
  induction fragment with
  | atomic leaf => exact atomic_rename _ leaf ρ α
  | @unary o t fragment ih =>
    obtain ⟨f⟩ := ih
    change Nonempty (BoundaryIso (unary o (term t)) (castDepth _ (unary o (term (Term.rename ρ.toFun α.toFun t)))))
    rw [castDepth_unary]
    exact ⟨unary_boundaryIso o f⟩

/-- Arbitrarily deep unary syntax stays in the proved fragment. -/
def unaryChain {k h} : List Unary → Term k h → Term k h
  | [],t => t
  | o::os,t => .unary o (unaryChain os t)

theorem unaryChain_fragment {k h} (ops : List Unary) {t : Term k h} (leaf : Atomic t) :
    UnaryFragment (unaryChain ops t) := by
  induction ops with
  | nil => exact .atomic leaf
  | cons o ops ih => exact .unary o ih

theorem unaryChain_rename {k h} (ops : List Unary) (t : Term k h) (leaf : Atomic t)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (term (unaryChain ops t))
      (castDepth (depth_rename (unaryChain ops t) ρ.toFun α.toFun)
        (term (Term.rename ρ.toFun α.toFun (unaryChain ops t))))) :=
  unaryFragment_rename _ (unaryChain_fragment ops leaf) ρ α
end Hypernets.Copying.Translation

namespace Hypernets.Copying.Examples
open Graph

/-- Original allocation subterm, with both ambient resource sorts retained. -/
def referenceOne_boundaryRename {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    BoundaryIso (referenceOne k h) (referenceOne k h) :=
  Translation.unary_boundaryIso .ref (Translation.constant_rename 0 ρ α (.nat 1))

/-- Original dereference clause follows a nontrivial atom renaming. -/
def dereferenceAtom_boundaryRename {k h} (ρ : Bijection (Fin k) (Fin k))
    (α : Bijection (Fin h) (Fin h)) (a : Fin h) :
    BoundaryIso (Translation.term (.unary .deref (.atom a) : Term k h))
      (Translation.term (.unary .deref (.atom (α.toFun a)) : Term k h)) :=
  Translation.unary_boundaryIso .deref (Translation.atom_rename 0 ρ α a)

/-- Original dereference of a bound variable follows its variable renaming. -/
def dereferenceVariable_boundaryRename {k h} (ρ : Bijection (Fin k) (Fin k))
    (α : Bijection (Fin h) (Fin h)) (i : Fin k) :
    BoundaryIso (Translation.term (.unary .deref (.var i) : Term k h))
      (Translation.term (.unary .deref (.var (ρ.toFun i)) : Term k h)) :=
  Translation.unary_boundaryIso .deref (Translation.variableTerm_rename 0 ρ α i)
end Hypernets.Copying.Examples
