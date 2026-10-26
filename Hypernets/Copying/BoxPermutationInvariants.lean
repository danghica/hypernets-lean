import Hypernets.Copying.FullTranslationRenaming

/-! Structural derivations retain all recursively checked primitive-label predicates.
They are not unrestricted equations on programs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Serial
open Graph
/-- Serial expansion contains exactly its two components' labels. -/
theorem allLabels_iff (P : Primitive → Prop) {d I J O} (G : Hypernet d I J) (H : Hypernet d J O) :
    AllLabels P (net G H) ↔ AllLabels P G ∧ AllLabels P H := by
  constructor
  · intro h
    cases d <;> exact ⟨fun e => h ⟨false,e⟩,fun e => h ⟨true,e⟩⟩
  · rintro ⟨g,h⟩; exact allLabels_net P g h
end Hypernets.Copying.Serial

namespace Hypernets.Copying.BoxPermutation.Derivation
open Graph

/-- Every generator and every congruence operation preserves all primitive restrictions. -/
theorem allLabels {d I O} {G H : Hypernet d I O} (s : Derivation G H) (P : Primitive → Prop) :
    AllLabels P G ↔ AllLabels P H := by
  induction s with
  | iso f => exact (BoundaryIso.ofDeepIso f).allLabels_iff P
  | rule r => exact r.allLabels P
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh
  | serial _ _ ih jh => exact (Serial.allLabels_iff P _ _).trans ((and_congr ih jh).trans (Serial.allLabels_iff P _ _).symm)
  | tensor _ _ ih jh =>
    exact (Net.Tensor.labels_iff _ _ (LabelAll P _)).trans
      ((and_congr ih jh).trans (Net.Tensor.labels_iff _ _ (LabelAll P _)).symm)
  | parallel B finite s ih =>
    constructor
    · intro h x; exact (ih x.1).mp (h ⟨x.1,·⟩) x.2
    · intro h x; exact (ih x.1).mpr (h ⟨x.1,·⟩) x.2
  | box _ ih =>
    constructor
    · intro h e; exact ih.mp (h (0 : Fin 1))
    · intro h e; exact ih.mpr (h (0 : Fin 1))
  | interfaces hi ho _ ih =>
    exact (Translation.allLabels_cast P hi ho _).trans (ih.trans (Translation.allLabels_cast P hi ho _).symm)
  | raise _ ih => exact (allLabels_raise_iff P _ _).trans (ih.trans (allLabels_raise_iff P _ _).symm)

theorem focusFree {d I O} {G H : Hypernet d I O} (s : Derivation G H) : FocusFree G ↔ FocusFree H := s.allLabels _
theorem holeFree {d I O} {G H : Hypernet d I O} (s : Derivation G H) : HoleFree G ↔ HoleFree H := s.allLabels _
theorem language {d I O} {G H : Hypernet d I O} (s : Derivation G H) : Translation.LanguageGraph G ↔ Translation.LanguageGraph H := s.allLabels _
end Hypernets.Copying.BoxPermutation.Derivation
