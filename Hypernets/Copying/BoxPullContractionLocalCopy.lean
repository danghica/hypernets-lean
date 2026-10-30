import Hypernets.Copying.BoxPullContractionAssembly
import Hypernets.Copying.BoxPullContractionViews
import Hypernets.Copying.BoxPullContractionResidual
import Hypernets.Copying.BoxPullContractionCopyCorrection
import Hypernets.Copying.UnrestrictedLocalTransfer

/-! Exhaustive actual copying transport for BPullC: all original copyable
constructors, retained/deep lambda boxes, and the literal sharing-algebra shallow case. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined
open BoxPullWeakening (PointedWitness)
namespace Copying

theorem primitive_transport {d I O} {A B : Hypernet d I O} (a : Fin I.length)
    (step : Rewrite A (.input a) B (.input a)) (primitive : BoxPermutation.PrimitiveFootprint A)
    (free : FocusFree A) (D : Decoration A) :
    ∃ H, Rewrite D.graph (Net.Expansion.host A D.fill (.input a)) H (.input a) ∧
      Nonempty (Residual B (.input a) H (.input a)) := by
  have resultFree := rewrite_focusFree step free
  have actual := step.rename (D.primitiveIso primitive) (DeepIso.refl B)
  rw [Decoration.primitiveIso_vertex] at actual
  exact ⟨B,actual,⟨Residual.direct (PointedWitness.input (FillingWitness.refl B resultFree) a)⟩⟩

variable {d n k h} (tree : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (D : Decoration (CopyRule.before tree (lambdaPayload B)))

abbrev boxes : Decoration (Translation.lambdaBox B) := D.serialRight.serialRight

noncomputable def sourceIso : DeepIso D.graph
    (Serial.net (CopyRule.tree tree (d+1))
      (Serial.net (primitiveNet (d+1) (.operation .lam)) ((boxes tree B D).fill (0 : Fin 1)))) :=
  D.serialIso.trans (Serial.congr (D.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.relabel _ _)).symm
    (D.serialRight.serialIso.trans (Serial.congr
      (D.serialRight.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.primitive _ _)).symm
      ((boxes tree B D).corollaIso _))))

theorem lambda_transport (free : FocusFree (CopyRule.before tree (lambdaPayload B)))
    : ∃ H, Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩)) H (.input ⟨0,by simp⟩) ∧
      Nonempty (Residual (CopyRule.after tree (lambdaPayload B)) (.input ⟨0,by simp⟩) H (.input ⟨0,by simp⟩)) := by
  have source := sourceIso tree B D
  cases ((boxes tree B D).pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (CopyRule.before tree (lambdaPayload B)) :=
      source.trans (Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) iso.symm))
    have step := (Rewrite.local (.copy tree _ (.lambda B))).rename f.symm (DeepIso.refl _)
    have resultFree := rewrite_focusFree (.local (.copy tree _ (.lambda B))) free
    exact ⟨_,step,⟨Residual.direct (PointedWitness.input (FillingWitness.refl _ resultFree) _)⟩⟩
  | @deep k h B C H body iso =>
    have f : DeepIso D.graph (CopyRule.before tree (lambdaPayload C)) :=
      source.trans (Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) iso.symm))
    have step := (Rewrite.local (.copy tree _ (.lambda C))).rename f.symm (DeepIso.refl _)
    exact ⟨_,step,⟨Residual.direct (PointedWitness.input (body.deepCopy tree) _)⟩⟩

  | @shallow k h s B H C bodyFree l r =>
    have leftSource : DeepIso (CopyRule.before tree (lambdaPayload B))
        (CopyRule.before tree (lambdaPayload (betaBody s C))) :=
      Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) l)
    have leftAlternative : Rewrite (CopyRule.before tree (lambdaPayload B)) (.input ⟨0,by simp⟩)
        (CopyRule.after tree (lambdaPayload (betaBody s C))) (.input ⟨0,by simp⟩) :=
      (Rewrite.local (.copy tree _ (.lambda (betaBody s C)))).rename leftSource.symm (DeepIso.refl _)
    obtain ⟨coherent⟩ := rewrite_deterministic (Rewrite.local (.copy tree _ (.lambda B))) leftAlternative
    have rightSource : DeepIso D.graph (contract s (CopyRule.before tree (lambdaPayload C))) :=
      source.trans ((Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) r.symm)).trans
        ((Serial.congr (DeepIso.refl _) (serial_contract s _ (Translation.lambdaBox C))).trans
          (serial_contract s _ (lambdaPayload C))))
    have step : Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩))
        (contract s (CopyRule.after tree (lambdaPayload C))) (.input ⟨0,by simp⟩) :=
      (copy_steps s tree C).2.rename rightSource.symm (DeepIso.refl _)
    have result := (Residual.copying s tree C bodyFree).congr coherent.graph.symm (DeepIso.refl _)
    exact ⟨_,step,⟨result⟩⟩

/-- Every constructor of original copyability is covered, including active
operation payloads and recursive representation changes. -/
theorem transport {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G)
    {n} (tree : ContractionTree .term (n+1)) (free : FocusFree (CopyRule.before tree G))
    (D : Decoration (CopyRule.before tree G)) :
    ∃ H, Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩)) H (.input ⟨0,by simp⟩) ∧
      Nonempty (Residual (CopyRule.after tree G) (.input ⟨0,by simp⟩) H (.input ⟨0,by simp⟩)) := by
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
    rw [Decoration.pullIso_host] at actual
    exact ⟨H,actual,⟨w.congr after (DeepIso.refl H)⟩⟩
end Copying

end Hypernets.Copying.BoxPullContraction
