import Hypernets.Copying.CopyingDoubleAt
import Hypernets.Copying.CopyingFillingReverse
import Hypernets.Copying.CopyingTemplateResidual

/-! The arbitrary-input copying residual is the original copying pair in the
retained branch, followed by the independently certified two-copy interchange. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDoubleAt
open Graph Combined CopyingInputPermutation
open BoxPullWeakening (PointedWitness)

variable {d n k h : Nat} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))
    (j : Fin (List.replicate (n+2) Wire.term).length)

/-- The actual order-exchange filling is supplied to the purely structural
assembly; it is used only to reverse the sharing correction, never to assert
symmetry of the directed copying relation. -/
noncomputable def residual (copyable : Copyable H) (free : FocusFree H)
    (interchange : FillingWitness SharingTreeAlgebra.template
      (CopyingDouble.afterSecond (normalized T j) H) (CopyingDouble.opposite (normalized T j) H)) :
    CopyingTemplate.Residual (leftAfter T H j) (.input j) (rightAfter T H j) (.input j) := {
  middle := net (CopyingDouble.opposite (normalized T j) H) (ordering j).symm
  point := .input j
  paired := PointedWitness.input
    ((CopyingDouble.oppositeWitness (normalized T j) H copyable free).inputPermutation (ordering j).symm) j
  correction := PointedWitness.input (interchange.reverseSharing.inputPermutation (ordering j).symm) j }

end Hypernets.Copying.CopyingDoubleAt
