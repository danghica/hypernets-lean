import Hypernets.Copying.ParametricityTailTensor
import Hypernets.Copying.ParametricityTailTransfer
import Hypernets.Copying.ParametricitySmallReadResidual
import Hypernets.Copying.ParametricityTemplate

/-! The complete private read is reattached to both actual remaining
Figure20 families. Its terminal correction contains a genuine parametricity
specimen with the selected term input weakened, not an assumed residual law. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallFamilyRead
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m₁ m₂} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))

def before : Hypernet (d+2) (List.replicate ((m₁+m₂)+1) .term) [] :=
  TailPrecompose.net (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))

noncomputable def after : State (d+2) (List.replicate ((m₁+m₂)+1) .term) [] :=
  TailPrecompose.state (leftFamily d m₁ m₂) (PrivateRead.after T (d+2))

/-- All unchanged left closures are reattached in their original order. -/
def corrected : Hypernet (d+2) (List.replicate ((m₁+m₂)+1) .term) [] :=
  TailPrecompose.net (leftFamily d m₁ m₂) (PrivateRead.result T (d+2))

/-- The same returned numeral precedes the unchanged ordered right family. -/
def counterpart : Hypernet (d+2) (List.replicate ((m₁+m₂)+1) .term) [] :=
  (Net.Tensor.net (ReadTail.numeral (d+2)) (rightFamily d m₁ m₂)).reboundary
    (by simp [List.replicate_succ]) rfl

noncomputable def residual : ReadResidual (after d T).1 (after d T).2.2
    (corrected d T) (.input ⟨0,by simp⟩) := by
  have lifted := TailPrecompose.residual (leftFamily d m₁ m₂)
    (labels_closed (leftFamily_labels d m₁ m₂)).1 (PrivateRead.fullResidual T (d+2))
  simpa only [TailPrecompose.right_zero,after,TailPrecompose.state,corrected] using lifted

/-- The remaining left private family is literally the original Figure20
family for the actual residual tree. Serial association only changes graph
representation, not the original sharing, store encoding, or translation. -/
noncomputable def residual_family_iso :
    DeepIso
      ((Net.Tensor.net (ReadTail.numeral (d+2)) (left d (CopyRule.residualTree T))).reboundary
        (by simp [List.replicate_succ]) rfl)
      (corrected d T) :=
  (CopyRule.reboundaryIso
    (BoxPermutation.tensor_congr (DeepIso.refl _)
      (Serial.Association.iso (leftFamily d m₁ m₂) (CopyRule.residual T (d+2)) (privateCell (d+2))))
    (by simp [List.replicate_succ]) rfl).trans
      (TailPrecompose.TensorResult.iso (leftFamily d m₁ m₂) (ReadTail.numeral (d+2))
        (Serial.net (CopyRule.residual T (d+2)) (privateCell (d+2))))

/-- A genuine remaining-family specimen. Both multiplicities are arbitrary,
including zero; its tree is the actual original tree with only the selected
input closed by the copying rule's literal weakening. -/
noncomputable def paired : FillingWitness template (corrected d T) (counterpart (m₁ := m₁) (m₂ := m₂) d) := by
  let numeral := FillingWitness.refl (T := template) (ReadTail.numeral (d+2))
    (by intro e m eq; cases eq)
  let family := FillingWitness.of_rel 0 (literal d (CopyRule.residualTree T))
  let raw := (numeral.tensor family).reboundary
    (J := List.replicate ((m₁+m₂)+1) .term) (K := []) (by simp [List.replicate_succ]) rfl
  exact raw.congr (residual_family_iso d T) (DeepIso.refl _)

noncomputable def pointed : PointedWitness template (corrected d T) (.input ⟨0,by simp⟩)
    (counterpart (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩) :=
  .input (paired d T) ⟨0,by simp⟩

/-- Exactly eight original transitions after beta, followed by the fully
constructed directed/exact correction and original remaining-family specimen. -/
theorem factorization :
    (machine (d+2) (List.replicate ((m₁+m₂)+1) .term) []).Steps 8
      ⟨before d T,(.search,.input ⟨0,by simp⟩)⟩ (after d T) ∧
    Nonempty (ReadResidual (after d T).1 (after d T).2.2 (corrected d T) (.input ⟨0,by simp⟩)) ∧
    Nonempty (PointedWitness template (corrected d T) (.input ⟨0,by simp⟩)
      (counterpart (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩)) := by
  have run := TailPrecompose.run (leftFamily d m₁ m₂) (PrivateRead.run T (d+2))
  change (machine _ _ _).Steps 8 ⟨before d T,(.search,TailPrecompose.rightInsert _ _ (.input ⟨0,by simp⟩))⟩ (after d T) at run
  rw [TailPrecompose.right_zero] at run
  exact ⟨run,⟨residual d T⟩,⟨pointed d T⟩⟩

end Hypernets.Copying.Parametricity.SmallFamilyRead
