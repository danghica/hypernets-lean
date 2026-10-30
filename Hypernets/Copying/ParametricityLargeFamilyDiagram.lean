import Hypernets.Copying.ParametricityLargeFamilySourceIso
import Hypernets.Copying.ParametricityLargeRightSource

/-! The complete one-versus-one larger-beta diagram starts at the actual
original application contexts around both full Figure 20 families. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeFamilyDiagram
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m n O} (d : Nat) (C : ContractionTree .term ((m+n)+1))
    (V : Hypernet (d+2) [.term] O)

def leftSource := ApplyFirst.net (LargeFamilySource.closedGraph d C) V
def rightSource := ApplyFirst.net (IsolatedFamily.largeRightFamily d m n) V

/-- The actual initial whole-family sources already have a genuine
original parametricity certificate, with the unchanged argument retained. -/
noncomputable def sourceWitness (free : FocusFree V) :
    FillingWitness template (leftSource d C V) (rightSource (m := m) (n := n) d V) :=
  ApplyFirst.witness _ _ (LargeFamilySource.familyWitness d C) free

/-- Opening a selected large abstraction reduces its family count by one
and increases the small count by one. Both original machine steps preserve
the entire unevaluated callback and every argument resource output. -/
theorem one_vs_one (stable : Stable V) :
    Rewrite (leftSource d C V) (.input ⟨0,by simp⟩)
      (LargeFamilyApplication.leftAfter d C V) (.input ⟨0,by simp⟩) ∧
    Rewrite (rightSource (m := m) (n := n) d V) (.input ⟨0,by simp⟩)
      (LargeFamilyApplication.rightAfter (m := m) (n := n) d V) (.input ⟨0,by simp⟩) ∧
    Nonempty (PointedWitness template (LargeFamilyApplication.leftAfter d C V) (.input ⟨0,by simp⟩)
      (LargeFamilyApplication.rightAfter (m := m) (n := n) d V) (.input ⟨0,by simp⟩)) := by
  obtain ⟨left,right,paired⟩ := LargeFamilyApplication.one_vs_one d C V stable
  have l := left.rename (LargeFamilySource.iso d C V).symm (DeepIso.refl _)
  have r := right.rename (LargeRightSource.iso (m := m) (n := n) d V).symm (DeepIso.refl _)
  exact ⟨l,r,paired⟩

end Hypernets.Copying.Parametricity.LargeFamilyDiagram
