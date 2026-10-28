import Hypernets.Copying.ConverseFillings
import Hypernets.Copying.OperationalCopyResidual

/-! Reversed structural certificates give residuals for the opposite of the
original specimen system. The original allowed context and both actual
coordinates are retained; no symmetry assumption is imposed on the template. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- Output closure is symmetric in the two actual graphs. -/
theorem PreTemplate.OutputClosed.converse {T : PreTemplate} (closed : T.OutputClosed) :
    T.converse.OutputClosed := by
  intro d I O G H pair
  exact (closed pair).symm

/-- Reverse a reversed specimen into the original template, preserving the
literal context, token, closed fillings and allowed-context proof. -/
def Specimen.unconverse {T : PreTemplate} {Allowed}
    (S : Specimen T.converse Allowed) : Specimen T Allowed where
  depth := S.depth
  context := S.context
  allowed := S.allowed
  free := S.free
  left := S.right
  right := S.left
  edges e := by simpa only [PreTemplate.converse] using (S.edges e).converse
  left_closed := S.right_closed
  right_closed := S.left_closed
  token := S.token
  term := S.term

/-- An equality-up-to residual for reversed certificates is exactly an
opposite-system residual for the original directed template. -/
theorem Specimens.converse_quasi {T : PreTemplate} {Allowed}
    (closed : T.OutputClosed) {s t : StateClass}
    (pair : (Specimens.system T.converse Allowed closed.converse).Quasi Eq Eq s t) :
    (Specimens.system T Allowed closed).opposite.Quasi Eq Eq s t := by
  intro hs ht
  obtain ⟨S,mode,leftRoot,rightRoot,left,right⟩ := pair hs ht
  exact ⟨S.unconverse,mode,leftRoot,rightRoot,left,right⟩

namespace RetainedFootprint
/-- A complete retained right occurrence and its reversed local residual
produce actual right/left rewrites and an original opposite quasi-specimen. -/
theorem converse_input_diamond {d J K} (C : Hypernet d [.term] []) {L R}
    {A X Y : Hypernet d J K} (f : Opening.Occurrence A (C.expand R)) {T : PreTemplate}
    (cert : ∀ e, DeepFillingEdge T C L R e) (avoid : AvoidsShallow C f.matchEmbedding)
    (free : FocusFree C) (i : Fin J.length) (typed : J[i] = .term)
    (rightLocal : Rewrite A (.input i) X (.input i))
    (leftLocal : Rewrite ((skeleton C f (fun e => (cert e).converse) avoid).expand
        (rightFamily C f (fun e => (cert e).converse) avoid))
      (Net.Expansion.host (skeleton C f (fun e => (cert e).converse) avoid)
        (rightFamily C f (fun e => (cert e).converse) avoid) (.input i)) Y (.input i))
    (w : FillingWitness T.converse X Y)
    (binding : BindingFree (residualGraft C f (fun e => (cert e).converse) avoid w))
    {v} (attached : f.ports (.input i) = Net.Expansion.host C R v)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand R) (Net.Expansion.host C R v)
      (afterGraph C f (fun e => (cert e).converse) avoid R X)
      (afterPort C f (fun e => (cert e).converse) avoid R X (.input i)) ∧
    Rewrite (C.expand L) (Net.Expansion.host C L v)
      (afterGraph C f (fun e => (cert e).converse) avoid L Y)
      (afterPort C f (fun e => (cert e).converse) avoid L Y (.input i)) ∧
    (Specimens.system T Specimens.bindingFreeContexts closed).opposite.Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f (fun e => (cert e).converse) avoid R X,
        (.search,afterPort C f (fun e => (cert e).converse) avoid R X (.input i))⟩)
      (StateClass.ofState ⟨d,afterGraph C f (fun e => (cert e).converse) avoid L Y,
        (.search,afterPort C f (fun e => (cert e).converse) avoid L Y (.input i))⟩) := by
  obtain ⟨right,left,residual⟩ := input_diamond C f (fun e => (cert e).converse) avoid free i typed
    rightLocal leftLocal w binding attached closed.converse rightClosed leftClosed
  exact ⟨right,left,Specimens.converse_quasi closed residual⟩
end RetainedFootprint
end Hypernets.Copying
