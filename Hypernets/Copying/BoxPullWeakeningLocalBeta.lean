import Hypernets.Copying.BoxPullWeakeningAssembly
import Hypernets.Copying.BoxPullWeakeningViews
import Hypernets.Copying.BoxPullWeakeningResidual
import Hypernets.Copying.UnrestrictedLocalTransfer

/-! Exhaustive actual beta transport for original BPullW fillings, including
retained, deep, and shallow boxes with the original stable argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined
namespace Beta
variable {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (D : Decoration (Application.before B G))

abbrev boxes : Decoration (Translation.lambdaBox B) := D.serialRight.tensorLeft.serialRight

noncomputable def sourceIso (stable : Stable G) :
    DeepIso D.graph (BoxPermutation.BetaDecoration.withBox G ((boxes B G D).fill (0 : Fin 1))) :=
  D.serialIso.trans (Serial.congr
    (D.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.primitive _ _)).symm
    (D.serialRight.tensorIso.trans (BoxPermutation.tensor_congr
      (D.serialRight.tensorLeft.serialIso.trans (Serial.congr
        (D.serialRight.tensorLeft.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.primitive _ _)).symm
        ((boxes B G D).corollaIso _)))
      (D.serialRight.tensorRight.primitiveIso (BoxPermutation.PrimitiveFootprint.stable stable)).symm)))

/-- The paired source has an actual beta step and a constructed original-template
local residual. The stable argument is the unchanged original graph. -/
theorem transport (stable : Stable G) (free : FocusFree (Application.before B G))
    : ∃ H, Rewrite D.graph (Net.Expansion.host (Application.before B G) D.fill (.input 0)) H (.input 0) ∧
      Nonempty (Residual (Application.after B G) (.input 0) H (.input 0)) := by
  have source := sourceIso B G D stable
  cases ((boxes B G D).pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (Application.before B G) :=
      source.trans (BoxPermutation.BetaDecoration.withBox_congr G iso.symm)
    have step := (Rewrite.local (.beta B G stable)).rename f.symm (DeepIso.refl _)
    have resultFree := rewrite_focusFree (.local (.beta B G stable)) free
    exact ⟨_,step,⟨Residual.direct (PointedWitness.input (FillingWitness.refl _ resultFree) 0)⟩⟩
  | @deep k h B C H body iso =>
    have f : DeepIso D.graph (Application.before C G) :=
      source.trans (BoxPermutation.BetaDecoration.withBox_congr G iso.symm)
    have step := (Rewrite.local (.beta C G stable)).rename f.symm (DeepIso.refl _)
    exact ⟨_,step,⟨Residual.direct (PointedWitness.input (UnrestrictedLocalTransfer.betaResidual template_paddingClosed body G stable) 0)⟩⟩
  | @shallow k h s B H C bodyFree l r =>
    have leftSource : DeepIso (Application.before B G) (Application.before (betaBody C s) G) :=
      BoxPermutation.BetaDecoration.withBox_congr G l
    have leftAlternative : Rewrite (Application.before B G) (.input 0)
        (Application.after (betaBody C s) G) (.input 0) :=
      (Rewrite.local (.beta (betaBody C s) G stable)).rename leftSource.symm (DeepIso.refl _)
    obtain ⟨coherent⟩ := rewrite_deterministic (Rewrite.local (.beta B G stable)) leftAlternative
    have rightSource : DeepIso D.graph (outsideBetaSource C G s) :=
      source.trans ((BoxPermutation.BetaDecoration.withBox_congr G r.symm).trans
        (outsideBetaSource_iso C G s))
    have step : Rewrite D.graph (Net.Expansion.host _ D.fill (.input 0))
        (outsideBetaAfter C G s) (.input 0) :=
      (beta_diamond C G s stable).2.1.rename rightSource.symm (DeepIso.refl _)
    have witness : FillingWitness template (Application.after B G) (outsideBetaAfter C G s) :=
      (FillingWitness.refl _ (rewrite_focusFree (.local (.beta B G stable)) free)).congr
        (DeepIso.refl _) (coherent.graph.trans (beta_successorIso C G s))
    exact ⟨_,step,⟨Residual.direct (PointedWitness.input witness 0)⟩⟩
end Beta


end Hypernets.Copying.BoxPullWeakening
