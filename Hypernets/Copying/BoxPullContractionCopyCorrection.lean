import Hypernets.Copying.BoxPullContractionCopyBoundary
import Hypernets.Copying.BoxPullContractionCopyCoverage
import Hypernets.Copying.BoxPullContractionResidual

/-! The copying overlap of literal BPullC: the duplicated original specimen
is followed by one independently proved exact sharing-tree correction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined
open BoxPullWeakening (PointedWitness)
namespace CopyRows
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

/-- Exhaustive complete incidence reconstruction identifies the corrected
whole graph with the literal outside-contraction reduct. -/
noncomputable def normalizationIso :
    DeepIso (contract s (CopyRule.after T H)) (corrected T s H) :=
  (normalizationOccurrence T s H).iso_of_edge_surjective
    (normalization_input T s H) (normalization_output T s H) (normalization_surjective T s H)

/-- One genuine sharing-algebra filling performs the whole-graph correction,
ending at the actual original copying reduct with contraction outside. -/
noncomputable def finalCorrection (free : FocusFree H) :
    FillingWitness SharingTreeAlgebra.template (CopyRule.after T (contract s H))
      (contract s (CopyRule.after T H)) := by
  have w := (correction T s H free).congr (DeepIso.refl _) (normalizationIso T s H).symm
  simpa only [merged_eq] using w
end CopyRows

namespace Residual
/-- The original copying overlap produces two genuine BPullC instances,
followed by the checked four-input sharing interchange. Both links preserve
the actual original search token and every unused contraction-tree branch. -/
noncomputable def copying {d n k h} (s : ShareSort) (tree : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (free : FocusFree B) :
    Residual (CopyRule.after tree (lambdaPayload (betaBody s B))) (.input ⟨0,by simp⟩)
      (contract s (CopyRule.after tree (lambdaPayload B))) (.input ⟨0,by simp⟩) := by
  have payloadFree : FocusFree (lambdaPayload B) :=
    ((contract_allLabels _ s _).mp (payloadWitness s B 0 free).focusFree.2).1
  exact ⟨CopyRule.after tree (contract s (lambdaPayload B)),.input ⟨0,by simp⟩,
    PointedWitness.input (copy_intermediateWitness s tree B free) _,
    PointedWitness.input (CopyRows.finalCorrection tree s (lambdaPayload B) payloadFree) _⟩
end Residual
end Hypernets.Copying.BoxPullContraction
