import Hypernets.Copying.NestedContextFilling

/-! A mixed, two-binder regression for actual graph filling and its certificates. -/
namespace Hypernets.Copying.Examples

/-- The hole can use both enclosing bound variables and all ambient resources. -/
def twoBinderContext (k h : Nat) : TermContext (k+2) h k h :=
  .lam (.unary .ref (.lam (.unary .deref .hole)))

theorem twoBinderContext_allowed (k h : Nat) : (twoBinderContext k h).UnaryLambda :=
  .lam (.unary .ref (.lam (.unary .deref .hole)))

/-- Substitution retains the two binders and the operations in their original order. -/
theorem twoBinderContext_fill (k h : Nat) (t : Term (k+2) h) :
    (twoBinderContext k h).fill t = .lam (.unary .ref (.lam (.unary .deref t))) := rfl

/-- Actual graph replacement below two boxes reconstructs the direct translation
of the displayed filled term; the very same address is sole and its host binding-free. -/
theorem twoBinderContext_graph_filling (k h name : Nat) (t : Term (k+2) h) :
    ∃ s : Site (ContextTranslation.graph (twoBinderContext k h) (Translation.depth t) name).2
        (Translation.depth t) [.term] (environmentInterface (k+2) h),
      SoleHole s ∧ BindingFree (ContextTranslation.graph (twoBinderContext k h) (Translation.depth t) name).2 ∧
      ContextTranslation.ScopedIso
        ⟨(ContextTranslation.graph (twoBinderContext k h) (Translation.depth t) name).1,
          plugAt s (Translation.term t)⟩
        (ContextTranslation.ofTerm (.lam (.unary .ref (.lam (.unary .deref t))))) :=
  ContextTranslation.unaryLambda_term_filling (twoBinderContext_allowed k h) name t
end Hypernets.Copying.Examples
