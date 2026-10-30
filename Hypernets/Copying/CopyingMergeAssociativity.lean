import Hypernets.Copying.CopyingMergeNormalization

/-! Associativity of actual original two-use resource merging follows from
complete three-branch normalization and genuine sharing-tree witnesses. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge
open Graph

/-- Both sides retain arbitrary original branch graphs and every canonical
weakening edge; the input order is fixed A, then B, then C. -/
noncomputable def assoc {d a b c k h}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))
    (C : Hypernet d (List.replicate c .term) (environmentInterface k h))
    (af : FocusFree A) (bf : FocusFree B) (cf : FocusFree C) :
    FillingWitness SharingTreeAlgebra.template (net (net A B) C)
      ((net A (net B C)).reboundary (by congr 1; omega) rfl) := by
  have w := (normalWitness A B C af bf cf).congr
    (Normalization.iso A B C false) (Normalization.iso A B C true)
  exact w
end Hypernets.Copying.CopyingMerge
