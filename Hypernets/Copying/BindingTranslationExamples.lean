import Hypernets.Copying.BindingTranslation
import Hypernets.Copying.ObservationExamples

set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Examples
open Graph

/-- A nested lambda/application/reference context, with a variable in the
hole scope bound by the enclosing lambda. -/
def nestedReferenceContext : TermContext 1 0 0 0 :=
  .lam (.appLeft (.unary .ref .hole) (.const .unit))

theorem nestedReferenceContext_bindingFree (d name : Nat) :
    BindingFree (ContextTranslation.graph nestedReferenceContext d name).2 :=
  BindingFree.context_graph _ _ _

/-- A contraction immediately before a term hole is one of the forbidden
copying configurations. Both of its source ports remain genuine inputs. -/
def contractionBeforeHole : Hypernet 0 [.term,.term] [] :=
  Serial.net (primitiveNet 0 (.contraction .term))
    (primitiveNet 0 (.hole ⟨0,[.term],[]⟩))

theorem contractionBeforeHole_not_bindingFree : ¬ BindingFree contractionBeforeHole := by
  intro free
  let a : contractionBeforeHole.Edge := ⟨false,(0 : Fin 1)⟩
  let b : contractionBeforeHole.Edge := ⟨true,(0 : Fin 1)⟩
  apply free.2 a b (by trivial) (by
    exact ⟨.input (0 : Fin 2),by change _ ∈ [_,_]; exact List.mem_cons_self⟩) ⟨_,rfl⟩
  refine ⟨b,⟨.internal (.inl (0 : Fin 1)),?_,?_⟩,.refl b⟩
  all_goals change _ ∈ [_]; exact List.mem_cons_self

/-- Increasing the finite box allowance cannot conceal an unsafe context. -/
theorem padded_contractionBeforeHole_not_bindingFree (d : Nat) :
    ¬ BindingFree (Translation.pad 0 d contractionBeforeHole) :=
  fun h => contractionBeforeHole_not_bindingFree ((BindingFree.pad_iff 0 d _).mp h)
end Hypernets.Copying.Examples
