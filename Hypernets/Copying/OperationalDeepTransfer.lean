import Hypernets.Copying.BindingFillingBeta
import Hypernets.Copying.BindingFillingPlug
import Hypernets.Copying.OperationalTemplateLaws
import Hypernets.Copying.FramedFillingTransfer

/-! Actual local and whole-host deep-copy transfer for the operational templates.
All residual admissibility proofs concern the common binding-free context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace FillingWitness
/-- Two actual local rewrites with a constructed admissible residual lift to
any original binding-free sourced-hole host, at its actual internal coordinate. -/
theorem binding_framed_rewrite {T : PreTemplate} {d}
    (C : Hypernet d [.term] []) (free : BindingFree C) (e : C.Edge)
    (hole : HoleLabel d (C.edgeLabel e))
    {G H A B : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length)
    (term : ((alphabet d).signature.input (C.edgeLabel e))[i] = .term)
    (leftStep : Rewrite G (.input i) A (.input i))
    (rightStep : Rewrite H (.input i) B (.input i))
    (w : FillingWitness T A B) (binding : BindingFree w.context) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.plug e G)) (rightClosed : HoleFree (C.plug e H)) :
    Rewrite (C.plug e G) (Net.Replacement.host C e G (C.sourcePort e i))
      (C.plug e A) (Net.Replacement.host C e A (C.sourcePort e i)) ∧
    Rewrite (C.plug e H) (Net.Replacement.host C e H (C.sourcePort e i))
      (C.plug e B) (Net.Replacement.host C e B (C.sourcePort e i)) ∧
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,C.plug e A,(.search,Net.Replacement.host C e A (C.sourcePort e i))⟩)
      (StateClass.ofState ⟨d,C.plug e B,(.search,Net.Replacement.host C e B (C.sourcePort e i))⟩) := by
  have left := Rewrite.plug C e leftStep
  have right := Rewrite.plug C e rightStep
  exact ⟨left,right,w.plug_binding_quasi C free e hole ⟨_,C.sourcePort_mem e i⟩ binding closed
    (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    (C.sourcePort e i) ((C.sourcePort_label e i).trans term)⟩
end FillingWitness

namespace OperationalTemplates.DeepTransfer
/-- Ordered input casts retain the selected input number. -/
def inputIndex {I J : List Wire} (hi : I = J) (i : Fin I.length) : Fin J.length :=
  ⟨i.val,by simpa only [← hi] using i.isLt⟩

theorem rewrite_input_cast {d I O J K} (hi : I = J) (ho : O = K)
    {G H : Hypernet d I O} (i : Fin I.length)
    (step : Rewrite G (.input i) H (.input i)) :
    Rewrite (Translation.castInterfaces hi ho G) (.input (inputIndex hi i))
      (Translation.castInterfaces hi ho H) (.input (inputIndex hi i)) := by
  cases hi; cases ho; exact step

theorem inputIndex_term {n J} (hi : List.replicate (n+1) Wire.term = J)
    (i : Fin (List.replicate (n+1) Wire.term).length) : J[inputIndex hi i] = .term := by
  cases hi
  exact List.getElem_replicate _

/-- Every all-deep lambda-copying case has matching original rewrites in any
binding-free host. The actual contraction tree, copied boxes, sharing
distributors and arbitrary nested operational occurrences are all retained. -/
theorem copy_framed_diamond {kind d n k h}
    (tree : ContractionTree .term (n+1))
    {B D : Hypernet d [.term] (environmentInterface (k+1) h)}
    (body : FillingWitness (template kind) B D) (binding : BindingFree body.context)
    (C : Hypernet (d+1) [.term] []) (free : BindingFree C) (e : C.Edge)
    (hole : HoleLabel (d+1) (C.edgeLabel e))
    (hi : List.replicate (n+1) .term = (alphabet (d+1)).signature.input (C.edgeLabel e))
    (ho : environmentInterface k h = (alphabet (d+1)).signature.output (C.edgeLabel e))
    (leftClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload B)))))
    (rightClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload D))))) :
    let i := inputIndex hi ⟨0,by simp⟩
    let left := Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload B))
    let right := Translation.castInterfaces hi ho (CopyRule.before tree (lambdaPayload D))
    let leftAfter := Translation.castInterfaces hi ho (CopyRule.after tree (lambdaPayload B))
    let rightAfter := Translation.castInterfaces hi ho (CopyRule.after tree (lambdaPayload D))
    Rewrite (C.plug e left) (Net.Replacement.host C e left (C.sourcePort e i))
      (C.plug e leftAfter) (Net.Replacement.host C e leftAfter (C.sourcePort e i)) ∧
    Rewrite (C.plug e right) (Net.Replacement.host C e right (C.sourcePort e i))
      (C.plug e rightAfter) (Net.Replacement.host C e rightAfter (C.sourcePort e i)) ∧
    (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi Eq Eq
      (StateClass.ofState ⟨d+1,C.plug e leftAfter,
        (.search,Net.Replacement.host C e leftAfter (C.sourcePort e i))⟩)
      (StateClass.ofState ⟨d+1,C.plug e rightAfter,
        (.search,Net.Replacement.host C e rightAfter (C.sourcePort e i))⟩) := by
  apply FillingWitness.binding_framed_rewrite C free e hole _ (inputIndex_term hi _)
    (rewrite_input_cast hi ho _ (.local (.copy tree _ (.lambda B))))
    (rewrite_input_cast hi ho _ (.local (.copy tree _ (.lambda D))))
    ((body.deepCopy tree).interfaces hi ho)
  · exact (body.deepCopy tree).interfaces_binding hi ho (body.deepCopy_binding tree binding)
  · exact leftClosed
  · exact rightClosed

/-- Every all-deep beta case has matching original rewrites in an arbitrary
binding-free sourced-hole host. Stability on the second side is proved from
the argument certificate, and the actual opened residual common context is
proved binding-free after its required depth padding. -/
theorem beta_framed_diamond {kind d k h O}
    {B D : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O}
    (body : FillingWitness (template kind) B D) (binding : BindingFree body.context)
    (arg : FillingWitness (template kind) G H) (stable : Stable G)
    (C : Hypernet (d+1) [.term] []) (free : BindingFree C) (e : C.Edge)
    (hole : HoleLabel (d+1) (C.edgeLabel e))
    (hi : [.term] = (alphabet (d+1)).signature.input (C.edgeLabel e))
    (ho : environmentInterface k h ++ O = (alphabet (d+1)).signature.output (C.edgeLabel e))
    (leftClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (Application.before B G))))
    (rightClosed : HoleFree (C.plug e (Translation.castInterfaces hi ho (Application.before D H)))) :
    let i := inputIndex hi 0
    let left := Translation.castInterfaces hi ho (Application.before B G)
    let right := Translation.castInterfaces hi ho (Application.before D H)
    let leftAfter := Translation.castInterfaces hi ho (Application.after B G)
    let rightAfter := Translation.castInterfaces hi ho (Application.after D H)
    Rewrite (C.plug e left) (Net.Replacement.host C e left (C.sourcePort e i))
      (C.plug e leftAfter) (Net.Replacement.host C e leftAfter (C.sourcePort e i)) ∧
    Rewrite (C.plug e right) (Net.Replacement.host C e right (C.sourcePort e i))
      (C.plug e rightAfter) (Net.Replacement.host C e rightAfter (C.sourcePort e i)) ∧
    (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi Eq Eq
      (StateClass.ofState ⟨d+1,C.plug e leftAfter,
        (.search,Net.Replacement.host C e leftAfter (C.sourcePort e i))⟩)
      (StateClass.ofState ⟨d+1,C.plug e rightAfter,
        (.search,Net.Replacement.host C e rightAfter (C.sourcePort e i))⟩) := by
  let residual := betaResidual body binding arg stable
  apply FillingWitness.binding_framed_rewrite C free e hole _ (inputIndex_term (n := 0) hi _)
    (rewrite_input_cast hi ho _ (.local (.beta B G stable)))
    (rewrite_input_cast hi ho _ (.local (.beta D H (stable.iso (stable_witness_iso arg stable)))))
    (residual.1.interfaces hi ho)
  · exact residual.1.interfaces_binding hi ho residual.2
  · exact leftClosed
  · exact rightClosed

end OperationalTemplates.DeepTransfer
end Hypernets.Copying
