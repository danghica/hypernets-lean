import Hypernets.Copying.SharingRootOrigin
import Hypernets.Copying.UnrestrictedCopyable

/-! Actual copyable payloads cannot overlap shallow sharing-template holes.
Their original retained skeleton therefore supplies a copyable paired payload. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingPayload
open Graph RetainedFootprint
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (f : Opening.Occurrence G (C.expand L))
include cert trees copyable

/-- Every actual outer copyable edge retains its original context owner;
sharing-template holes can contribute only weakening or contraction edges. -/
theorem avoids : AvoidsShallow C f.matchEmbedding := by
  intro e name hole
  have outer := (Copyable.outer_equiv d (f.label e)).mp (copyable.outer_labels e)
  rcases (cert (f.edges e).1).origin with ⟨⟨copy⟩,_⟩ | ⟨h,label,pair⟩
  · have actual : (C.expand L).edgeLabel (f.edges e) = primitiveLabel d (.hole name) := by
      change (L (f.edges e).1).edgeLabel (f.edges e).2 = _
      rw [copy.only (f.edges e).2]
      exact (copy.primitive _).mpr hole
    rw [actual] at outer
    cases d <;> exact outer
  · obtain ⟨s,n,_,_,left,_⟩ := (trees pair).shape
    have actual := left (f.edges e).2
    change (C.expand L).edgeLabel (f.edges e) = _ ∨ (C.expand L).edgeLabel (f.edges e) = _ at actual
    rcases actual with actual | actual
    all_goals rw [actual] at outer
    all_goals cases d <;> exact outer

/-- The actual paired footprint is copyable, including any changed original
lambda body. The witness keeps the original retained context skeleton. -/
theorem paired (free : FocusFree C) :
    let avoid := avoids C cert trees copyable f
    Copyable ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) ∧
      Nonempty (FillingWitness T G ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))) := by
  dsimp only
  let avoid := avoids C cert trees copyable f
  let D := UnrestrictedFootprint.decoration C f cert avoid free
  have sourceFree := f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free).1
  obtain ⟨right,_⟩ := UnrestrictedDecoration.copyable_payload copyable sourceFree D
  exact ⟨right.rename (UnrestrictedFootprint.decorationIso C f cert avoid free),
    ⟨RetainedFootprint.witness C f cert avoid free⟩⟩

end Hypernets.Copying.SharingPayload
