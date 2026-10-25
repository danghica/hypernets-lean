import Hypernets.Copying.PaddingPlug
import Hypernets.Copying.NestedFillingExamples

/-! Combined regressions: deep sites, padding and ordered application assembly. -/
namespace Hypernets.Copying.Examples

/-- An occurrence under arbitrary boxes can be padded twice and placed in an
application's left argument. The actual address is sole and filling commutes
with both padding steps and the full application translation. -/
theorem paddedApplicationLeft_filling {d k h r U V}
    {C : Hypernet d [.term] (environmentInterface k h)}
    (s : Site C r U V) (sole : SoleHole s)
    (H : Hypernet (d+2) [.term] (environmentInterface k h)) (free : HoleFree H)
    (A : Hypernet r U V) :
    let address := Translation.applicationLeftSite H (Padding.padSite s 2)
    SoleHole address ∧ Nonempty (DeepIso
      (plugAt address (Translation.pad r 2 A))
      (Translation.application (Translation.pad d 2 (plugAt s A)) H)) := by
  refine ⟨Translation.applicationLeftSite_sole H free _ (Padding.padSite_sole s sole 2),?_⟩
  exact ⟨(Translation.applicationLeft_filling H _ _).trans
    (Translation.application_congr (Padding.pad_filling s A 2).symm (DeepIso.refl H))⟩

/-- The symmetric regression checks the other component tag and its ordered
boundary exchange; the fixed left argument may itself contain boxes. -/
theorem paddedApplicationRight_filling {d k h r U V}
    {C : Hypernet d [.term] (environmentInterface k h)}
    (s : Site C r U V) (sole : SoleHole s)
    (G : Hypernet (d+2) [.term] (environmentInterface k h)) (free : HoleFree G)
    (A : Hypernet r U V) :
    let address := Translation.applicationRightSite G (Padding.padSite s 2)
    SoleHole address ∧ Nonempty (DeepIso
      (plugAt address (Translation.pad r 2 A))
      (Translation.application G (Translation.pad d 2 (plugAt s A)))) := by
  refine ⟨Translation.applicationRightSite_sole G free _ (Padding.padSite_sole s sole 2),?_⟩
  exact ⟨(Translation.applicationRight_filling G _ _).trans
    (Translation.application_congr (DeepIso.refl G) (Padding.pad_filling s A 2).symm)⟩
end Hypernets.Copying.Examples
