import Hypernets.Copying.BindingFillingPadding
import Hypernets.Copying.BindingSplice
import Hypernets.Copying.BindingFillingWitness
import Hypernets.Copying.OperationalTemplateLaws

/-! The original bound-output splice preserves admissible residual contexts.
A stable argument's operational filling certificate is rigid, so its common
context is chosen as that actual stable graph. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

/-- Splicing certificates uses the actual common bound-output splice. -/
theorem splice_context {d F O} {B C : Hypernet d [.term] (.term :: F)}
    {G H : Hypernet d [.term] O} (body : FillingWitness T B C) (arg : FillingWitness T G H) :
    (body.splice arg).context = Application.splice body.context arg.context := by
  cases d
  all_goals
    apply congrArg (Net.expand (Application.splicePattern _ F O))
    funext b
    cases b <;> rfl

/-- The stable argument suffix cannot send an ancestry path back into an
operational occurrence in the opened body. -/
theorem splice_binding {d F O} {B C : Hypernet d [.term] (.term :: F)}
    {G H : Hypernet d [.term] O} (body : FillingWitness T B C) (arg : FillingWitness T G H)
    (binding : BindingFree body.context) (closed : HoleFree arg.context) :
    BindingFree (body.splice arg).context := by
  rw [splice_context]
  exact BindingFree.splice_suffix _ _ binding arg.free closed

end FillingWitness

namespace OperationalTemplates.DeepTransfer
open Graph

/-- Flat stability rules out every operational contribution in the argument.
The replacement certificate therefore uses the unchanged actual left graph
as its common context and the proved representation isomorphism on the right. -/
noncomputable def stableArgument {kind d O} {G H : Hypernet d [.term] O}
    (arg : FillingWitness (template kind) G H) (stable : Stable G) :
    FillingWitness (template kind) G H :=
  (FillingWitness.refl G stable.focusFree).congr (DeepIso.refl _) (stable_witness_iso arg stable)

theorem stableArgument_closed {kind d O} {G H : Hypernet d [.term] O}
    (arg : FillingWitness (template kind) G H) (stable : Stable G) :
    HoleFree (stableArgument arg stable).context := stable.holeFree

/-- Opening a genuinely paired boxed body pads its entire original common
context, exposes exactly bound output zero, and splices the stable argument.
The binding-free proof is stored with the actual residual certificate. -/
noncomputable def betaResidual {kind d k h O}
    {B D : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O}
    (body : FillingWitness (template kind) B D) (binding : BindingFree body.context)
    (arg : FillingWitness (template kind) G H) (stable : Stable G) :
    {w : FillingWitness (template kind) (Application.after B G) (Application.after D H) //
      BindingFree w.context} := by
  let raised := body.raiseBinding (template_paddingClosed kind) binding
  let opened := raised.1.interfaces rfl (BoxPermutation.Opening.interface k h)
  exact ⟨opened.splice (stableArgument arg stable),
    opened.splice_binding (stableArgument arg stable)
      (raised.1.interfaces_binding _ _ raised.2) (stableArgument_closed arg stable)⟩

end OperationalTemplates.DeepTransfer
end Hypernets.Copying
