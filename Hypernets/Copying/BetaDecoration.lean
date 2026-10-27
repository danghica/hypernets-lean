import Hypernets.Copying.LambdaBoxView

/-! Exhaustive whole-redex beta transport, including retained, shallow, and deep
box contributions and the original mandatory stable argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

noncomputable def tensor_congr {d I O J K} {A B : Hypernet d I O} {C D : Hypernet d J K}
    (f : DeepIso A B) (g : DeepIso C D) : DeepIso (Net.Tensor.net A C) (Net.Tensor.net B D) :=
  Net.ParallelIso.iso (fun b => match b with | false => f | true => g) _ _

namespace BetaDecoration
variable {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O)

def withBox (X : Hypernet (d+1) [.thunk 1] (environmentInterface k h)) :=
  Serial.net (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (Serial.net (primitiveNet (d+1) (.operation .lam)) X) G)

noncomputable def withBox_congr {X Y : Hypernet (d+1) [.thunk 1] (environmentInterface k h)}
    (f : DeepIso X Y) : DeepIso (withBox G X) (withBox G Y) :=
  Serial.congr (DeepIso.refl _) (tensor_congr (Serial.congr (DeepIso.refl _) f) (DeepIso.refl G))

variable (D : Decoration (Application.before B G))

abbrev boxes : Decoration (Translation.lambdaBox B) := D.serialRight.tensorLeft.serialRight

/-- All other local contributions collapse by their actual primitive footprints. -/
noncomputable def sourceIso (stable : Stable G) : DeepIso D.graph (withBox G ((boxes B G D).fill (0 : Fin 1))) :=
  D.serialIso.trans (Serial.congr
    (D.serialLeft.primitiveIso (PrimitiveFootprint.primitive _ _)).symm
    (D.serialRight.tensorIso.trans (tensor_congr
      (D.serialRight.tensorLeft.serialIso.trans (Serial.congr
        (D.serialRight.tensorLeft.serialLeft.primitiveIso (PrimitiveFootprint.primitive _ _)).symm
        ((boxes B G D).corollaIso _)))
      (D.serialRight.tensorRight.primitiveIso (PrimitiveFootprint.stable stable)).symm)))

/-- The compensation moves through the unchanged lambda, tensor and application wiring. -/
noncomputable def compensated (C : Hypernet d [.term] (environmentInterface (k+1) h))
    (p : TypedPermutation (environmentInterface k h)) :
    DeepIso (withBox G (InterfacePermutation.net (Translation.lambdaBox C) p.symm))
      (InterfacePermutation.net (Application.before C G) (p.append (.refl O)).symm) := by
  have closure := InterfacePermutation.serial (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox C) p.symm
  have operands := (tensor_congr closure (DeepIso.refl G)).trans
    (InterfacePermutation.tensor_left (Application.closure C) G p.symm)
  have whole := (Serial.congr (DeepIso.refl (primitiveNet (d+1) (.operation .app))) operands).trans
    (InterfacePermutation.serial _ (Net.Tensor.net (Application.closure C) G) (p.symm.append (.refl O)))
  simpa only [withBox,Application.before,TypedPermutation.append_symm,TypedPermutation.symm_refl] using whole

/-- Every classified beta overlap has an actual right rewrite and an original
pointed residual. No assumption of robustness or translation correctness occurs. -/
theorem transport (stable : Stable G) (free : FocusFree (Application.before B G)) :
    ∃ H w, Rewrite D.graph (Net.Expansion.host (Application.before B G) D.fill (.input 0)) H w ∧
      Nonempty (PointedFilling (Application.after B G) (.input 0) H w) := by
  have bodyFree : FocusFree B := by
    have closures := (Serial.allLabels_iff _ _ _).mp free
    have closure := (Net.Tensor.labels_iff _ _ _).mp closures.2
    have boxFree := (Serial.allLabels_iff _ _ _).mp closure.1
    exact (Translation.allLabels_cast _ rfl _ B).mp (boxFree.2 (0 : Fin 1))
  have source := sourceIso B G D stable
  cases ((boxes B G D).pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (Application.before B G) := source.trans (withBox_congr G iso.symm)
    have s := (Rewrite.local (.beta B G stable)).rename f.symm (DeepIso.refl _)
    exact ⟨_,.input 0,s,⟨PointedFilling.input (FillingWitness.refl _ (Application.after_labels _ B G bodyFree stable.focusFree)) 0⟩⟩
  | @deep C H body iso =>
    have f : DeepIso D.graph (Application.before C G) := source.trans (withBox_congr G iso.symm)
    have s := (Rewrite.local (.beta C G stable)).rename f.symm (DeepIso.refl _)
    exact ⟨_,.input 0,s,⟨PointedFilling.input (body.betaAfter template_paddingClosed (FillingWitness.refl G stable.focusFree)) 0⟩⟩
  | @shallow C H p body action iso =>
    have f := source.trans ((withBox_congr G iso.symm).trans (compensated G C p))
    have s := (InterfacePermutation.rewrite (p.append (.refl O)).symm
      (Rewrite.local (.beta C G stable))).rename f.symm (DeepIso.refl _)
    have residual := MixedBeta.residualWitness body p (FillingWitness.refl G stable.focusFree) bodyFree stable action
    exact ⟨_,.input 0,s,⟨PointedFilling.input residual 0⟩⟩
end BetaDecoration
end Hypernets.Copying.BoxPermutation
