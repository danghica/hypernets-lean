import Hypernets.Copying.CopyingDoubleSymmetry

/-! Two original Figure 17 copies commute up to the independently proved
sharing-tree template. Both full canonical distributors remain in each graph,
all three payload copies are retained, and every external input is fixed. -/
namespace Hypernets.Copying.CopyingDouble

/-- Copying original inputs zero and one in either order produces a genuine
sharing-template filling witness. This theorem includes arbitrary remaining
inputs and arbitrary ordered term/atom environments, including empty forests.
It asserts no isomorphism between different sharing-tree presentations. -/
noncomputable def interchange {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h)) (free : FocusFree H) :
    FillingWitness SharingTreeAlgebra.template (afterSecond T H) (opposite T H) :=
  (Frame.witness H free
    (CopyRule.residualTree (CopyRule.residualTree T))
    (CopyRule.residualTree (CopyRule.residualTree (CopyingInputPermutation.reordered T (exchangeInputs n))))).congr
      (Source.iso T H)
      ((Symmetry.iso H _).trans
        (CopyingInputPermutation.congr
          (Source.iso (CopyingInputPermutation.reordered T (exchangeInputs n)) H)
          (exchangeInputs n)))

end Hypernets.Copying.CopyingDouble
