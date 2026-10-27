import Hypernets.Copying.FillingTransport

/-! BPerm itself, not only structural derivations, is closed under depth padding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- The original output action commutes with the original representation padding. -/
theorem InterfacePermutation.raise {d I O} (G : Hypernet d I O) (p : TypedPermutation O) :
    Copying.raise d (InterfacePermutation.net G p) =
      InterfacePermutation.net (Copying.raise d G) p := by
  rw [← Padding.graph_eq_raise,← Padding.graph_eq_raise]
  unfold Padding.graph Net.relabel InterfacePermutation.net
  congr 1
  all_goals
    funext e
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    cases v <;> rfl

namespace BoxPermutation

theorem Step.raise {d I O} {G H : Hypernet d I O} (pair : Step G H) :
    Step (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | permute B p =>
    simpa only [Padding.box,InterfacePermutation.raise] using Step.permute (Copying.raise _ B) p

theorem UpToIso.raise {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness l pair r => exact .witness (Padding.congr l) pair.raise (Padding.congr r)

theorem template_raise {d I O} {G H : Hypernet d I O} (pair : template.Rel G H) :
    template.Rel (Copying.raise d G) (Copying.raise d H) :=
  ⟨pair.1.raise,(allLabels_raise_iff _ _ _).mpr pair.2⟩
end BoxPermutation
end Hypernets.Copying
