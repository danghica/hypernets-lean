import Hypernets.Copying.Stability
import Hypernets.Copying.Copyability
import Hypernets.Copying.Translation

namespace Hypernets.Copying.Examples
open Graph

/-- A unary active operation is copyable but is not a stable graph. -/
theorem unary_copyable_not_stable (d : Nat) (o : Unary) :
    Copyable (k := 1) (h := 0) (primitiveNet d (.operation (.unary o))) ∧
    ¬ Stable (primitiveNet d (.operation (.unary o))) := by
  refine ⟨.unary d o,?_⟩
  intro h
  exact h.outputs ⟨0,by simp [primitiveSignature, Operation.outputs]⟩

/-- This is a permitted copy payload, not a stable graph: it has an internal thunk vertex. -/
theorem lambdaPayload_not_stable {d k h}
    (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    ¬ Stable (lambdaPayload G) := by
  intro stable
  exact Stable.no_internal stable.labels (.inl ⟨0,by decide⟩)

/-- Every translated lambda body yields a copyable, globally focus-free payload. -/
theorem translated_lambda_payload {k h} (t : Term (k+1) h) :
    Copyable (lambdaPayload (Translation.term t)) ∧
    FocusFree (lambdaPayload (Translation.term t)) ∧
    HoleFree (lambdaPayload (Translation.term t)) := by
  have lang := Copyable.lambdaPayload_language (Translation.term_language t)
  exact ⟨.lambda _,Translation.language_focusFree lang,Translation.language_holeFree lang⟩

/-- The unchanged right-hand program factors through a copyable payload and the
paper's single-use distributors. No distributors are dropped. -/
theorem constantResult_copyable_factor (k h : Nat) :
    ∃ P : Hypernet 2 [.term] (environmentInterface k h),
      Copyable P ∧ Translation.constantResult k h = Serial.net P (Translation.singleUse 2 k h) := by
  refine ⟨lambdaPayload (Translation.term (Term.seq (.app (.var 0) (.const .unit))
    (.const (.nat 1)) : Term (k+1) h)),.lambda _,?_⟩
  rfl

/-- The unit corolla is stable and has its uniquely determined outer edge. -/
theorem unit_stable_unique (d : Nat) :
    Stable (primitiveNet d (.operation (.const .unit))) ∧
    ∃ e : (primitiveNet d (.operation (.const .unit))).Edge, ∀ f, f = e :=
  ⟨Stable.constant d .unit,Stable.exists_unique_edge (Stable.constant d .unit)⟩

end Hypernets.Copying.Examples
