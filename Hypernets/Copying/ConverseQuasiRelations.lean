import Hypernets.Copying.ConverseSpecimenTransfer

/-! Reversing the actual recursive specimen preserves arbitrary directed
auxiliary relations, not just equality at the two endpoints. -/
namespace Hypernets.Copying
open Combined

/-- The original common context and token are unchanged when a reversed
template specimen is viewed in the original opposite specimen system. -/
theorem Specimens.converse_quasi_rel {T : PreTemplate} {Allowed}
    (closed : T.OutputClosed) {A B : StateClass → StateClass → Prop} {s t : StateClass}
    (pair : (Specimens.system T.converse Allowed closed.converse).Quasi A B s t) :
    (Specimens.system T Allowed closed).opposite.Quasi A B s t := by
  intro hs ht
  obtain ⟨S,mode,leftRoot,rightRoot,left,right⟩ := pair hs ht
  exact ⟨S.unconverse,mode,leftRoot,rightRoot,left,right⟩

end Hypernets.Copying
