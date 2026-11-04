import Hypernets.Copying.ParametricityReadDiagram
import Hypernets.Copying.ParametricitySmallBareDiagram
import Hypernets.Copying.CopyingResidualBoundary

/-! The constructed bare smaller-family overlap, packaged with its exact
original opening/read/correction evidence for arbitrary selected transport. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallBareDiagram
open Graph Combined
variable {m₁ m₂} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))

/-- The smaller beta case has eight post-beta steps. Its entire correction
and remaining-family witness come from the proved original private read. -/
theorem readDiagram : Nonempty (ReadDiagram (left d T) (.input ⟨0,by simp⟩)
    (right (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩) 8) := by
  obtain ⟨result,steps,mode,⟨correction⟩,⟨paired⟩⟩ := after_opening d T
  refine ⟨{
    leftVariables := 1, leftAtoms := 0, leftBody := readBody (d+1)
    rightVariables := 0, rightAtoms := 0, rightBody := oneBody (d+1)
    leftOpened := SmallBareApplication.opened d T
    leftPoint := .input ⟨0,by simp⟩
    rightOpened := SmallBareApplication.counterpart (m₁ := m₁) (m₂ := m₂) d
    rightPoint := .input ⟨0,by simp⟩
    left := leftOpening d T, right := rightOpening (m₁ := m₁) (m₂ := m₂) d
    result := result.1, resultPoint := result.2.2
    run := ?_
    corrected := SmallBareApplication.corrected d T
    correctedPoint := .input ⟨0,by simp⟩
    correction := correction, paired := paired
    typed := ?_ }⟩
  · simpa only [← mode] using steps
  · refine correction.labels.trans ?_
    change (List.replicate ((m₁+m₂)+1) Wire.term ++ [])[0] = Wire.term
    simp

/-- Removing only the harmless append-empty interface presentation gives the
canonical bare source expected by the arbitrary original-member permutation. -/
theorem normalized : Nonempty (ReadDiagram
    (BareApplyFirst.net (SmallBareSource.closedGraph d T)) (.input ⟨0,by simp⟩)
    (BareApplyFirst.net (IsolatedFamily.smallRightFamily d m₁ m₂)) (.input ⟨0,by simp⟩) 8) := by
  obtain ⟨p⟩ := readDiagram d T
  have q := p.reboundary (List.append_nil _) rfl
  change ReadDiagram
    (((BareApplyFirst.net (SmallBareSource.closedGraph d T)).reboundary (List.append_nil _).symm rfl).reboundary (List.append_nil _) rfl) (.input ⟨0,by simp⟩)
    (((BareApplyFirst.net (IsolatedFamily.smallRightFamily d m₁ m₂)).reboundary (List.append_nil _).symm rfl).reboundary (List.append_nil _) rfl) (.input ⟨0,by simp⟩) 8 at q
  rw [CopyingTemplate.reboundary_cancel,CopyingTemplate.reboundary_cancel] at q
  exact ⟨q⟩
end Hypernets.Copying.Parametricity.SmallBareDiagram
