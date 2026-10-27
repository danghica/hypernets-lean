import Hypernets.Copying.AtomicBoxView

/-! Reassociate edgewise transformations through the actual serial, parallel,
and corolla constructions used by the local operation rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.Decoration
open Graph Combined

noncomputable def corollaIso {d} (a : (alphabet d).Symbol)
    (D : Decoration (Net.corolla (alphabet d).signature a)) : DeepIso D.graph (D.fill 0) :=
  (ExpandedRewrite.peel _ D.fill 0 (fun b ne => False.elim (ne (Fin.ext (by omega))))).trans
    (DeepIso.ofIso (Net.corolla_plug_iso a (D.fill 0)))

def serialLeft {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : Decoration (Serial.net G H)) : Decoration G := by
  cases d <;> exact D.component (Serial.pattern _ I J O) (Serial.filling G H) false

def serialRight {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : Decoration (Serial.net G H)) : Decoration H := by
  cases d <;> exact D.component (Serial.pattern _ I J O) (Serial.filling G H) true

noncomputable def serialIso {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : Decoration (Serial.net G H)) : DeepIso D.graph (Serial.net D.serialLeft.graph D.serialRight.graph) := by
  have grouped := D.groupedIso (Serial.pattern d I J O) (Serial.filling G H)
  apply grouped.trans
  apply Net.ExpansionIso.iso
  intro b
  cases d <;> cases b <;> exact DeepIso.refl _

def tensorLeft {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : Decoration (Net.Tensor.net G H)) : Decoration G where
  fill e := D.fill ⟨false,e⟩
  pair e := D.pair ⟨false,e⟩

def tensorRight {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : Decoration (Net.Tensor.net G H)) : Decoration H where
  fill e := D.fill ⟨true,e⟩
  pair e := D.pair ⟨true,e⟩

noncomputable def tensorIso {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : Decoration (Net.Tensor.net G H)) : DeepIso D.graph (Net.Tensor.net D.tensorLeft.graph D.tensorRight.graph) := by
  have grouped := DeepIso.ofIso (Net.ParallelExpansion.iso (Net.Tensor.family G H) (Net.Tensor.boundary I O J K)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (fun b e => D.fill ⟨b,e⟩))
  apply grouped.trans
  apply Net.ParallelIso.iso
  intro b
  cases b <;> exact DeepIso.refl _

/-- Pull a decoration through equality transport of boundary lists. -/
def unboundary {d I O J K} {G : Hypernet d I O} (hi : I = J) (ho : O = K)
    (D : Decoration (G.reboundary hi ho)) : Decoration G := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using D
end Hypernets.Copying.BoxPermutation.Decoration
