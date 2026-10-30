import Hypernets.Copying.CopyingSelectedRetained
import Hypernets.Copying.CopyCoherence

/-! Normalize only the outer presentation of an actual copyable payload.
The full original source occurrence and exact selected token are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening

/-- Transport the selected token while keeping the actual active edge,
orientation, side wire, complete payload occurrence, and normal form literal. -/
def SuccessorMatch.atToken {d I O k h} {G : Hypernet d I O} {v w : G.Vertex}
    {H : Hypernet d [.term] (environmentInterface k h)}
    (a : SuccessorMatch G v H) (eq : v = w) : SuccessorMatch G w H where
  normal := a.normal
  payload := a.payload
  active := a.active
  right := a.right
  other := a.other
  active_label := a.active_label
  active_source := eq ▸ a.active_source
  resolves := eq ▸ a.resolves

/-- Every supplied original copying occurrence has a full-label occurrence
with a normalized outer payload and the identical original selected input.
Recursive box contents and the original contraction tree are unchanged. -/
theorem normalized_occurrence {d I O m k h} {G : Hypernet d I O}
    (T : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (f : Occurrence (before T H) G) :
    ∃ V : Hypernet d [.term] (environmentInterface k h), ∃ normal : NormalForm V,
      ∃ g : Occurrence (before T V) G,
        g.ports (.input ⟨0,by simp⟩) = f.ports (.input ⟨0,by simp⟩) := by
  obtain ⟨V,⟨normal⟩,⟨iso⟩⟩ := normal_form copyable
  let changed := (Occurrence.ofIso (before_congr (Net.Iso.refl T.net) iso.symm)).comp f
  exact ⟨V,normal,changed,rfl⟩

end Hypernets.Copying.CopyRule
