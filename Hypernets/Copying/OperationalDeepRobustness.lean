import Hypernets.Copying.OperationalDeepTransfer

/-! Exact quantitative robustness conclusions for constructed binding-free
deep-copy and beta diamonds, including independently represented successors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace FillingWitness
/-- An actual binding-free host diamond discharges the complete forward
robustness conclusion for any independently supplied source successor. -/
theorem binding_framed_robust_case {T : PreTemplate} (closed : T.OutputClosed)
    {d} {G H A B : Hypernet d [.term] []} {g h a b}
    (diamond : Rewrite G g A a ∧ Rewrite H h B b ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
        (StateClass.ofState ⟨d,A,(.search,a)⟩) (StateClass.ofState ⟨d,B,(.search,b)⟩))
    (Q P R : CostOrder) {u}
    (next : StateClass.machine.step (StateClass.ofState ⟨d,G,(.rewrite,g)⟩) u) :
    ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,H,(.rewrite,h)⟩) y ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) x y :=
  matching_robust_case Q P R (StateClass.project (.lift (.rewrite diamond.1)))
    (StateClass.project (.lift (.rewrite diamond.2.1))) diamond.2.2 next

/-- The converse uses the same genuine residual specimen with exchanged
projections. Neither a reversed template rule nor a new stability assumption
is required; the quantitative witness is again zero versus one further step. -/
theorem binding_framed_robust_case_opposite {T : PreTemplate} (closed : T.OutputClosed)
    {d} {G H A B : Hypernet d [.term] []} {g h a b}
    (diamond : Rewrite G g A a ∧ Rewrite H h B b ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
        (StateClass.ofState ⟨d,A,(.search,a)⟩) (StateClass.ofState ⟨d,B,(.search,b)⟩))
    (Q P R : CostOrder) {u}
    (next : StateClass.machine.step (StateClass.ofState ⟨d,H,(.rewrite,h)⟩) u) :
    ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,G,(.rewrite,g)⟩) y ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) x y :=
  matching_robust_case Q P R (StateClass.project (.lift (.rewrite diamond.2.1)))
    (StateClass.project (.lift (.rewrite diamond.1))) (quasi_exchange _ diamond.2.2) next
end FillingWitness

namespace OperationalTemplates.DeepTransfer
/-- The original rewrite-mode class at a sourced-hole host's actual coordinate. -/
noncomputable def framedSource {d} (C : Hypernet d [.term] []) (e : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length) : StateClass :=
  StateClass.ofState ⟨d,C.plug e G,(.rewrite,Net.Replacement.host C e G (C.sourcePort e i))⟩

section Copying
variable {kind d n k h} (tree : ContractionTree .term (n+1))
    {B D : Hypernet d [.term] (environmentInterface (k+1) h)}
    (body : FillingWitness (template kind) B D) (binding : BindingFree body.context)
    (C : Hypernet (d+1) [.term] []) (free : BindingFree C) (e : C.Edge)
    (hole : HoleLabel (d+1) (C.edgeLabel e))
    (hi : List.replicate (n+1) .term = (alphabet (d+1)).signature.input (C.edgeLabel e))
    (ho : environmentInterface k h = (alphabet (d+1)).signature.output (C.edgeLabel e))
    (leftClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload B)))))
    (rightClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload D)))))

include body binding free hole leftClosed rightClosed

/-- The exact forward robustness conclusion for all-deep lambda copying,
with arbitrary original contraction trees and internal host coordinates. -/
theorem copy_robust_case (Q P R : CostOrder) {u}
    (next : StateClass.machine.step
      (framedSource C e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload B)))
        (inputIndex hi ⟨0,by simp⟩)) u) :
    ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
      StateClass.machine.Steps l
        (framedSource C e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload D)))
          (inputIndex hi ⟨0,by simp⟩)) y ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) x y :=
  FillingWitness.binding_framed_robust_case _
    (copy_framed_diamond tree body binding C free e hole hi ho leftClosed rightClosed) Q P R next

/-- Converse deep-copy robustness preserves those same original specimens. -/
theorem copy_robust_case_opposite (Q P R : CostOrder) {u}
    (next : StateClass.machine.step
      (framedSource C e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload D)))
        (inputIndex hi ⟨0,by simp⟩)) u) :
    ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
      StateClass.machine.Steps l
        (framedSource C e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload B)))
          (inputIndex hi ⟨0,by simp⟩)) y ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) x y :=
  FillingWitness.binding_framed_robust_case_opposite _
    (copy_framed_diamond tree body binding C free e hole hi ho leftClosed rightClosed) Q P R next
end Copying

section Beta
variable {kind d k h O}
    {B D : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O}
    (body : FillingWitness (template kind) B D) (binding : BindingFree body.context)
    (arg : FillingWitness (template kind) G H) (stable : Stable G)
    (C : Hypernet (d+1) [.term] []) (free : BindingFree C) (e : C.Edge)
    (hole : HoleLabel (d+1) (C.edgeLabel e))
    (hi : [.term] = (alphabet (d+1)).signature.input (C.edgeLabel e))
    (ho : environmentInterface k h ++ O = (alphabet (d+1)).signature.output (C.edgeLabel e))
    (leftClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (Application.before B G))))
    (rightClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (Application.before D H))))

include body binding arg stable free hole leftClosed rightClosed

/-- The exact forward robustness conclusion for the all-deep original beta
rule, preserving its stable argument premise and binding-free observations. -/
theorem beta_robust_case (Q P R : CostOrder) {u}
    (next : StateClass.machine.step
      (framedSource C e (Translation.castInterfaces hi ho (Application.before B G)) (inputIndex hi 0)) u) :
    ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
      StateClass.machine.Steps l
        (framedSource C e (Translation.castInterfaces hi ho (Application.before D H)) (inputIndex hi 0)) y ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) x y :=
  FillingWitness.binding_framed_robust_case _
    (beta_framed_diamond body binding arg stable C free e hole hi ho leftClosed rightClosed) Q P R next

/-- Converse deep-beta robustness derives the right stability premise from
the original paired argument and exchanges the proved residual specimen. -/
theorem beta_robust_case_opposite (Q P R : CostOrder) {u}
    (next : StateClass.machine.step
      (framedSource C e (Translation.castInterfaces hi ho (Application.before D H)) (inputIndex hi 0)) u) :
    ∃ k l x y, Q.rel (1+k) l ∧ StateClass.machine.Steps k u x ∧
      StateClass.machine.Steps l
        (framedSource C e (Translation.castInterfaces hi ho (Application.before B G)) (inputIndex hi 0)) y ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) x y :=
  FillingWitness.binding_framed_robust_case_opposite _
    (beta_framed_diamond body binding arg stable C free e hole hi ho leftClosed rightClosed) Q P R next
end Beta

end OperationalTemplates.DeepTransfer
end Hypernets.Copying
