import Hypernets.Copying.CopyingInputContext
import Hypernets.Copying.AddressedWitness
import Hypernets.Copying.CopyingSelectedInput

/-! The actual input-permutation graph context transports recursive paired
fillings without changing the underlying template relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph

/-- Relabelled external input positions are part of the common graph context;
they require no extra constructor or closure assumption on the pre-template. -/
noncomputable def inputPermutation {T : PreTemplate} {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (p : TypedPermutation I) :
    FillingWitness T (CopyingInputPermutation.net G p) (CopyingInputPermutation.net H p) := by
  cases d
  all_goals
    exact (w.plug (CopyingInputPermutation.frame _ I O p)
      (by intro e mode eq; cases eq)
      (CopyingInputPermutation.frameEdge _ I O p)).congr
      (by simpa only [CopyingInputPermutation.inFrame,Net.reboundary_refl] using CopyingInputPermutation.frameIso G p)
      (by simpa only [CopyingInputPermutation.inFrame,Net.reboundary_refl] using CopyingInputPermutation.frameIso H p)

end Hypernets.Copying.FillingWitness

namespace Hypernets.Copying.CopyingSelectedInput
open Graph

/-- An arbitrary-input copying step itself has an independently constructed
recursive copying-template certificate. The original relation still uses input
zero; the actual common context supplies precisely the compensated permutation. -/
noncomputable def witness {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (i : Fin (List.replicate (n+1) Wire.term).length)
    (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness CopyingTemplate.template (CopyRule.before T H) (after T H i) :=
  ((FillingWitness.of_rel 0 (CopyingTemplate.literal
    (CopyingInputPermutation.reordered T (permutation i)) H copyable free)).inputPermutation
      (permutation i).symm).congr (CopyingInputPermutation.beforeIso T H (permutation i)).symm
        (DeepIso.refl _)

end Hypernets.Copying.CopyingSelectedInput
