import Hypernets.Copying.BetaDecoration

/-! All copying payloads transported by actual rewrites and original residual
specimens, including both copies of a deeply transformed lambda body. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.CopyDecoration
open Graph Combined

variable {d n k h} (T : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (D : Decoration (CopyRule.before T (lambdaPayload B)))

abbrev boxes : Decoration (Translation.lambdaBox B) := D.serialRight.serialRight

noncomputable def sourceIso : DeepIso D.graph
    (Serial.net (CopyRule.tree T (d+1))
      (Serial.net (primitiveNet (d+1) (.operation .lam)) ((boxes T B D).fill (0 : Fin 1)))) :=
  D.serialIso.trans (Serial.congr (D.serialLeft.primitiveIso (PrimitiveFootprint.relabel _ _)).symm
    (D.serialRight.serialIso.trans (Serial.congr
      (D.serialRight.serialLeft.primitiveIso (PrimitiveFootprint.primitive _ _)).symm
      ((boxes T B D).corollaIso _))))

theorem lambda_transport (free : FocusFree (CopyRule.before T (lambdaPayload B))) :
    ∃ H w, Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩)) H w ∧
      Nonempty (PointedFilling (CopyRule.after T (lambdaPayload B)) (.input ⟨0,by simp⟩) H w) := by
  have bodyFree : FocusFree B := by
    have payload := (Serial.allLabels_iff _ _ _).mp free
    have boxFree := (Serial.allLabels_iff _ _ _).mp payload.2
    exact (Translation.allLabels_cast _ rfl _ B).mp (boxFree.2 (0 : Fin 1))
  have source := sourceIso T B D
  cases ((boxes T B D).pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (CopyRule.before T (lambdaPayload B)) :=
      source.trans (Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) iso.symm))
    have s := (Rewrite.local (.copy T _ (.lambda B))).rename f.symm (DeepIso.refl _)
    exact ⟨_,.input ⟨0,by simp⟩,s,⟨PointedFilling.input
      (FillingWitness.refl _ (rewrite_focusFree (.local (.copy T _ (.lambda B))) free)) ⟨0,by simp⟩⟩⟩
  | @deep C H body iso =>
    have f : DeepIso D.graph (CopyRule.before T (lambdaPayload C)) :=
      source.trans (Serial.congr (DeepIso.refl _) (Serial.congr (DeepIso.refl _) iso.symm))
    have s := (Rewrite.local (.copy T _ (.lambda C))).rename f.symm (DeepIso.refl _)
    exact ⟨_,.input ⟨0,by simp⟩,s,⟨PointedFilling.input (body.deepCopy T) ⟨0,by simp⟩⟩⟩
  | @shallow C H p body action iso =>
    have closure := (Serial.congr (DeepIso.refl (primitiveNet (d+1) (.operation .lam))) iso.symm).trans
      (InterfacePermutation.serial _ (Translation.lambdaBox C) p.symm)
    have f := source.trans ((Serial.congr (DeepIso.refl _) closure).trans
      (InterfacePermutation.serial (CopyRule.tree T (d+1)) (lambdaPayload C) p.symm))
    have s := (InterfacePermutation.rewrite p.symm (Rewrite.local (.copy T _ (.lambda C)))).rename f.symm (DeepIso.refl _)
    exact ⟨_,.input ⟨0,by simp⟩,s,⟨PointedFilling.input (Copying.residualWitness T body p bodyFree action) ⟨0,by simp⟩⟩⟩

/-- Copyability's complete operation alphabet is covered; renaming reuses the
original copying rule and transports the whole residual graph. -/
theorem transport {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G)
    {n} (T : ContractionTree .term (n+1)) (free : FocusFree (CopyRule.before T G))
    (D : Decoration (CopyRule.before T G)) :
    ∃ H w, Rewrite D.graph (Net.Expansion.host _ D.fill (.input ⟨0,by simp⟩)) H w ∧
      Nonempty (PointedFilling (CopyRule.after T G) (.input ⟨0,by simp⟩) H w) := by
  induction copyable with
  | instanceEdge d =>
    exact primitive_transport (.local (.copy T _ (.instanceEdge d)))
      (PrimitiveFootprint.serial (PrimitiveFootprint.relabel _ _) (PrimitiveFootprint.primitive _ _)) free D
  | constant d c =>
    exact primitive_transport (.local (.copy T _ (.constant d c)))
      (PrimitiveFootprint.serial (PrimitiveFootprint.relabel _ _) (PrimitiveFootprint.primitive _ _)) free D
  | application d =>
    exact primitive_transport (.local (.copy T _ (.application d)))
      (PrimitiveFootprint.serial (PrimitiveFootprint.relabel _ _) (PrimitiveFootprint.primitive _ _)) free D
  | unary d o =>
    exact primitive_transport (.local (.copy T _ (.unary d o)))
      (PrimitiveFootprint.serial (PrimitiveFootprint.relabel _ _) (PrimitiveFootprint.primitive _ _)) free D
  | binary d o =>
    exact primitive_transport (.local (.copy T _ (.binary d o)))
      (PrimitiveFootprint.serial (PrimitiveFootprint.relabel _ _) (PrimitiveFootprint.primitive _ _)) free D
  | lambda B => exact lambda_transport T B D free
  | @rename d k h A B f copyable ih =>
    let before := CopyRule.before_congr (Net.Iso.refl T.net) f
    let after := CopyRule.after_congr (Net.Iso.refl T.net) f
    obtain ⟨H,w,s,⟨p⟩⟩ := ih ((allLabels_iso_iff _ before).mpr free) (D.pull before)
    have r := s.rename (D.pullIso before) (DeepIso.refl H)
    rw [Decoration.pullIso_host] at r
    have ident : Port.map (DeepIso.refl H).vertices.toFun w = w := by cases w <;> rfl
    rw [ident] at r
    have residual := p.congr after (DeepIso.refl H)
    rw [ident] at residual
    exact ⟨H,w,r,⟨residual⟩⟩
end Hypernets.Copying.BoxPermutation.CopyDecoration
