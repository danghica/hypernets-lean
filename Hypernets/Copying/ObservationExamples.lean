import Hypernets.Copying.Observations
import Hypernets.Copying.BindingExamples

set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Examples
open Graph

/-- Closing observations are nonempty: a closed term can be observed in the
identity hole context, at every allowance. -/
def identityClosingContext (d : Nat) : ClosingContext d 0 0 := by
  cases d with
  | zero =>
    refine ⟨0,primitiveNet 0 (.hole ⟨0,[.term],[]⟩),Site.shallow (primitiveNet 0 (.hole ⟨0,[.term],[]⟩)) (by simp [primitiveNet]; exact (0 : Fin 1)),?_,hole_bindingFree 0 _⟩
    refine ⟨⟨_,rfl⟩,?_⟩
    intro f ne
    exact False.elim (ne (Fin.ext (by omega)))
  | succ n =>
    refine ⟨(n+1),primitiveNet (n+1) (.hole ⟨0,[.term],[]⟩),Site.shallow (primitiveNet (n+1) (.hole ⟨0,[.term],[]⟩)) (by simp [primitiveNet]; exact (0 : Fin 1)),?_,hole_bindingFree (n+1) _⟩
    refine ⟨⟨_,rfl⟩,?_⟩
    intro f ne
    exact False.elim (ne (Fin.ext (by omega)))

/-- An enclosing lambda binds the variable already present in the annotated
hole's scope; filling retains its original de Bruijn index. -/
theorem bound_hole_translation :
    ContextTranslation.apply (TermContext.lam (.hole : TermContext 1 0 1 0))
      (ContextTranslation.ofTerm (.var 0)) =
    ContextTranslation.ofTerm (Term.lam (.var 0) : Term 0 0) :=
  ContextTranslation.apply_ofTerm _ _

/-- Application contexts reconstruct the original left proposition program,
with its allocation term and lambda body exactly as specified. -/
theorem privateCell_context_factor (k h : Nat) :
    ContextTranslation.apply
      (TermContext.appRight
        (.lam (.lam (Term.seq (.app (.var 0) (.const .unit)) (.unary .deref (.var 1)))))
        (.hole : TermContext k h k h))
      (ContextTranslation.ofTerm (.unary .ref (.const (.nat 1)))) =
    ContextTranslation.ofTerm (Term.privateCell k h) :=
  ContextTranslation.apply_ofTerm _ _

/-- The right proposition program is an abstraction context around its exact
original body, including the sequencing sugar and its inner binder. -/
theorem constantResult_context_factor (k h : Nat) :
    ContextTranslation.apply (TermContext.lam (.hole : TermContext (k+1) h (k+1) h))
      (ContextTranslation.ofTerm (Term.seq (.app (.var 0) (.const .unit)) (.const (.nat 1)))) =
    ContextTranslation.ofTerm (Term.constantResult k h) :=
  ContextTranslation.apply_ofTerm _ _
end Hypernets.Copying.Examples
