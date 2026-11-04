import Hypernets.Copying.ParametricitySmallBareSourceIso
import Hypernets.Copying.ParametricitySmallRightBare

/-! The complete smaller-family beta diagram exposes the argument wire.
Its sources are genuine original parametricity fillings, its openings are
source-relative certificates, and its eight post-beta steps and corrections
are constructed from the unchanged copying/store machine. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallBareDiagram
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m₁ m₂} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))

def left := (BareApplyFirst.net (SmallBareSource.closedGraph d T)).reboundary
  (List.append_nil _).symm rfl
def right := (BareApplyFirst.net (IsolatedFamily.smallRightFamily d m₁ m₂)).reboundary
  (List.append_nil _).symm rfl

/-- The same bare original application context contains the complete original
left and right Figure20 families; no graph supplying the argument is included. -/
noncomputable def sourceWitness : FillingWitness template (left d T) (right (m₁ := m₁) (m₂ := m₂) d) :=
  (BareApplyFirst.witness _ (SmallBareSource.familyWitness d T)).reboundary
    (List.append_nil _).symm rfl

theorem left_token : SmallBareApplication.token d T = .input ⟨0,by simp⟩ :=
  CompleteMatchCut.replace_input _ _ _ _ (SmallBareApplication.body_input d T)
theorem right_token : SmallBareApplication.rightToken (m₁ := m₁) (m₂ := m₂) d = .input ⟨0,by simp⟩ :=
  CompleteMatchCut.replace_input _ _ _ _ (SmallBareApplication.rightBody_input (m₁ := m₁) (m₂ := m₂) d)

/-- The original read-body opening leaves its bound weakening attached to the
exposed argument wire and retains every original private sharing branch. -/
noncomputable def leftOpening : Application.OpeningCertificate (left d T)
    (SmallBareApplication.opened d T) (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) (readBody (d+1)) := by
  have c := (SmallBareApplication.opening d T).rename (SmallBareSource.iso d T).symm (DeepIso.refl _)
  rw [left_token] at c
  exact c

/-- The original constant-body opening retains the identical argument wire
and all remaining right closures, with no stability assertion about the wire. -/
noncomputable def rightOpening : Application.OpeningCertificate
    (right (m₁ := m₁) (m₂ := m₂) d) (SmallBareApplication.counterpart (m₁ := m₁) (m₂ := m₂) d)
    (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) (oneBody (d+1)) := by
  have c := (SmallBareApplication.rightOpening (m₁ := m₁) (m₂ := m₂) d).rename
    (SmallRightBare.iso (m := m₁) (n := m₂) d).symm (DeepIso.refl _)
  rw [right_token] at c
  exact c

/-- After the two independently enabled original beta steps, the left takes
exactly eight further original transitions and the right takes zero. The
actual correction and original remaining-family specimen are both supplied. -/
theorem after_opening :
    ∃ target, (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) [Wire.term]).Steps 8
      ⟨SmallBareApplication.opened d T,(.search,.input ⟨0,by simp⟩)⟩ target ∧
      target.2.1 = .search ∧
      Nonempty (ReadResidual target.1 target.2.2 (SmallBareApplication.corrected d T) (.input ⟨0,by simp⟩)) ∧
      Nonempty (PointedWitness template (SmallBareApplication.corrected d T) (.input ⟨0,by simp⟩)
        (SmallBareApplication.counterpart (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩)) :=
  SmallBareApplication.read_factorization d T
end Hypernets.Copying.Parametricity.SmallBareDiagram
