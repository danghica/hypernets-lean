import Hypernets.Copying.ParametricityLargeBareSourceIso
import Hypernets.Copying.ParametricityLargeRightBare

/-! The actual whole-family large beta sources, with their argument wire
exposed. Both original openings leave a genuine pointed parametricity
residual; no graph supplying the argument is included in the local cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeBareDiagram
open Graph Opening Combined
variable {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1))

def left := BareApplyFirst.net (LargeBareSource.closedGraph d C)
def right := BareApplyFirst.net (IsolatedFamily.largeRightFamily d m n)

noncomputable def sourceWitness : FillingWitness template (left d C) (right (m := m) (n := n) d) :=
  BareApplyFirst.witness _ (LargeBareSource.familyWitness d C)

/-- The original large read-body opening retains the complete unevaluated
callback and private tree, while exposing the original argument wire. -/
noncomputable def leftOpening : Application.OpeningCertificate (left d C)
    (LargeBareApplication.leftAfter d C) (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩)
    (callReadBody d) :=
  (LargeBareApplication.left_certificate d C).rename
    (LargeBareSource.iso d C).symm (DeepIso.refl _)

/-- The original right opening keeps the same callback and argument boundary. -/
noncomputable def rightOpening : Application.OpeningCertificate
    (right (m := m) (n := n) d) (LargeBareApplication.rightAfter (m := m) (n := n) d)
    (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) (callOneBody d) :=
  (LargeBareApplication.right_certificate (m := m) (n := n) d).rename
    (LargeRightBare.iso (m := m) (n := n) d).symm (DeepIso.refl _)

/-- No post-opening transition is needed: both actual targets retain the
original family relation, with one fewer large and one more small member. -/
noncomputable def residual : BoxPullWeakening.PointedWitness template
    (LargeBareApplication.leftAfter d C) (.input ⟨0,by simp⟩)
    (LargeBareApplication.rightAfter (m := m) (n := n) d) (.input ⟨0,by simp⟩) :=
  LargeBareApplication.pointed d C

end Hypernets.Copying.Parametricity.LargeBareDiagram
