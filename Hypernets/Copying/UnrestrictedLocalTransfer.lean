import Hypernets.Copying.UnrestrictedLocalViews

/-! Retained/deep local transport for an arbitrary template. This permits
actual reversed operational certificates without reversing any machine rule.
Beta uses proved padding closure; copying needs no template closure law. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.UnrestrictedLocalTransfer
open Graph Combined

/-- Pad and open the actual paired body, then splice the unchanged stable
argument. The original common body context may contain binding paths to holes. -/
noncomputable def betaResidual {T : PreTemplate} (padding : T.PaddingClosed) {d k h O}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (body : FillingWitness T B C)
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    FillingWitness T (Application.after B G) (Application.after C G) :=
  ((body.raise padding).interfaces rfl (BoxPermutation.Opening.interface k h)).splice
    (FillingWitness.refl G stable.focusFree)

namespace Beta
variable {T : PreTemplate} {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (D : UnrestrictedDecoration T (Application.before B G))

abbrev boxes : UnrestrictedDecoration T (Translation.lambdaBox B) := D.serialRight.tensorLeft.serialRight

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
theorem transport (padding : T.PaddingClosed) (stable : Stable G) (free : FocusFree (Application.before B G))
    : ∃ H, Rewrite D.graph (Net.Expansion.host (Application.before B G) D.fill (.input 0)) H (.input 0) ∧
      Nonempty (FillingWitness T (Application.after B G) H) := by
  have source := sourceIso B G D stable
  cases ((boxes B G D).pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (Application.before B G) :=
      source.trans (BoxPermutation.BetaDecoration.withBox_congr G iso.symm)
    have step := (Rewrite.local (.beta B G stable)).rename f.symm (DeepIso.refl _)
    have resultFree := rewrite_focusFree (.local (.beta B G stable)) free
    exact ⟨_,step,⟨FillingWitness.refl _ resultFree⟩⟩
  | @deep C H body iso =>
    have f : DeepIso D.graph (Application.before C G) :=
      source.trans (BoxPermutation.BetaDecoration.withBox_congr G iso.symm)
    have step := (Rewrite.local (.beta C G stable)).rename f.symm (DeepIso.refl _)
    exact ⟨_,step,⟨betaResidual padding body G stable⟩⟩
end Beta

namespace Copying
variable {T : PreTemplate}

theorem primitive_transport {d I O} {A B : Hypernet d I O} (a : Fin I.length)
    (step : Rewrite A (.input a) B (.input a)) (primitive : BoxPermutation.PrimitiveFootprint A)
    (free : FocusFree A) (D : UnrestrictedDecoration T A) :
    ∃ H, Rewrite D.graph (Net.Expansion.host A D.fill (.input a)) H (.input a) ∧
      Nonempty (FillingWitness T B H) := by
  have resultFree := rewrite_focusFree step free
  have actual := step.rename (D.primitiveIso primitive) (DeepIso.refl B)
  rw [UnrestrictedDecoration.primitiveIso_vertex] at actual
  exact ⟨B,actual,⟨FillingWitness.refl B resultFree⟩⟩

variable {d n k h} (tree : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (D : UnrestrictedDecoration T (CopyRule.before tree (lambdaPayload B)))

abbrev boxes : UnrestrictedDecoration T (Translation.lambdaBox B) := D.serialRight.serialRight

noncomputable def sourceIso : DeepIso D.graph
    (Serial.net (CopyRule.tree tree (d+1))
      (Serial.net (primitiveNet (d+1) (.operation .lam)) ((boxes tree B D).fill (0 : Fin 1)))) :=
  D.serialIso.trans (Serial.congr (D.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.relabel _ _)).symm
    (D.serialRight.serialIso.trans (Serial.congr
      (D.serialRight.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.primitive _ _)).symm
      ((boxes tree B D).corollaIso _))))

theorem lambda_transport (free : FocusFree (CopyRule.before tree (lambdaPayload B)))
    : ∃ H, Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩)) H (.input ⟨0,by simp⟩) ∧
      Nonempty (FillingWitness T (CopyRule.after tree (lambdaPayload B)) H) := by
  have source := sourceIso tree B D
  cases ((boxes tree B D).pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (CopyRule.before tree (lambdaPayload B)) :=
      source.trans (Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) iso.symm))
    have step := (Rewrite.local (.copy tree _ (.lambda B))).rename f.symm (DeepIso.refl _)
    have resultFree := rewrite_focusFree (.local (.copy tree _ (.lambda B))) free
    exact ⟨_,step,⟨FillingWitness.refl _ resultFree⟩⟩
  | @deep C H body iso =>
    have f : DeepIso D.graph (CopyRule.before tree (lambdaPayload C)) :=
      source.trans (Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) iso.symm))
    have step := (Rewrite.local (.copy tree _ (.lambda C))).rename f.symm (DeepIso.refl _)
    exact ⟨_,step,⟨body.deepCopy tree⟩⟩

/-- Every constructor of original copyability is covered, including active
operation payloads and recursive representation changes. -/
theorem transport {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G)
    {n} (tree : ContractionTree .term (n+1)) (free : FocusFree (CopyRule.before tree G))
    (D : UnrestrictedDecoration T (CopyRule.before tree G)) :
    ∃ H, Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩)) H (.input ⟨0,by simp⟩) ∧
      Nonempty (FillingWitness T (CopyRule.after tree G) H) := by
  induction copyable with
  | instanceEdge d =>
    exact primitive_transport _ (.local (.copy tree _ (.instanceEdge d)))
      (BoxPermutation.PrimitiveFootprint.serial (BoxPermutation.PrimitiveFootprint.relabel _ _)
        (BoxPermutation.PrimitiveFootprint.primitive _ _)) free D
  | constant d c =>
    exact primitive_transport _ (.local (.copy tree _ (.constant d c)))
      (BoxPermutation.PrimitiveFootprint.serial (BoxPermutation.PrimitiveFootprint.relabel _ _)
        (BoxPermutation.PrimitiveFootprint.primitive _ _)) free D
  | application d =>
    exact primitive_transport _ (.local (.copy tree _ (.application d)))
      (BoxPermutation.PrimitiveFootprint.serial (BoxPermutation.PrimitiveFootprint.relabel _ _)
        (BoxPermutation.PrimitiveFootprint.primitive _ _)) free D
  | unary d o =>
    exact primitive_transport _ (.local (.copy tree _ (.unary d o)))
      (BoxPermutation.PrimitiveFootprint.serial (BoxPermutation.PrimitiveFootprint.relabel _ _)
        (BoxPermutation.PrimitiveFootprint.primitive _ _)) free D
  | binary d o =>
    exact primitive_transport _ (.local (.copy tree _ (.binary d o)))
      (BoxPermutation.PrimitiveFootprint.serial (BoxPermutation.PrimitiveFootprint.relabel _ _)
        (BoxPermutation.PrimitiveFootprint.primitive _ _)) free D
  | lambda B => exact lambda_transport tree B D free
  | @rename d k h A B f copyable ih =>
    let before := CopyRule.before_congr (Net.Iso.refl tree.net) f
    let after := CopyRule.after_congr (Net.Iso.refl tree.net) f
    obtain ⟨H,step,⟨w⟩⟩ := ih ((allLabels_iso_iff _ before).mpr free) (D.pull before)
    have actual := step.rename (D.pullIso before) (DeepIso.refl H)
    rw [UnrestrictedDecoration.pullIso_host] at actual
    exact ⟨H,actual,⟨w.congr after (DeepIso.refl H)⟩⟩
end Copying
end Hypernets.Copying.UnrestrictedLocalTransfer
