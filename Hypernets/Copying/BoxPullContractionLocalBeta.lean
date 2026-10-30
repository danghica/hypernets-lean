import Hypernets.Copying.BoxPullContractionAssembly
import Hypernets.Copying.BoxPullContractionViews
import Hypernets.Copying.BoxPullContractionResidual
import Hypernets.Copying.UnrestrictedLocalTransfer

/-! Exhaustive actual beta transport for original BPullC fillings, including
retained, deep, and shallow boxes with the original stable argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined
open BoxPullWeakening (PointedWitness)
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
    have leftSource : DeepIso (Application.before B G) (Application.before (betaBody s C) G) :=
      BoxPermutation.BetaDecoration.withBox_congr G l
    have leftAlternative : Rewrite (Application.before B G) (.input 0)
        (Application.after (betaBody s C) G) (.input 0) :=
      (Rewrite.local (.beta (betaBody s C) G stable)).rename leftSource.symm (DeepIso.refl _)
    obtain ⟨coherent⟩ := rewrite_deterministic (Rewrite.local (.beta B G stable)) leftAlternative
    have outside : DeepIso
        (BoxPermutation.BetaDecoration.withBox G (contract s (Translation.lambdaBox C)))
        (outsideBetaSource s C G) := by
      change DeepIso (boxedApplication (contract s (Translation.lambdaBox C)) G) _
      rw [contract_eq]
      exact boxedApplication_output _ _ _
    have rightSource : DeepIso D.graph (outsideBetaSource s C G) :=
      source.trans ((BoxPermutation.BetaDecoration.withBox_congr G r.symm).trans
        outside)
    have step : Rewrite D.graph (Net.Expansion.host _ D.fill (.input 0))
        (outsideBetaAfter s C G) (.input 0) :=
      (beta_diamond s C G stable).2.1.rename rightSource.symm (DeepIso.refl _)
    have witness : FillingWitness template (Application.after B G) (outsideBetaAfter s C G) :=
      (FillingWitness.refl _ (rewrite_focusFree (.local (.beta B G stable)) free)).congr
        (DeepIso.refl _) (coherent.graph.trans (beta_successorIso s C G))
    exact ⟨_,step,⟨Residual.direct (PointedWitness.input witness 0)⟩⟩
end Beta


end Hypernets.Copying.BoxPullContraction
