import Hypernets.Copying.BoxPullWeakeningReverseCopyable
import Hypernets.Copying.MinimalCopyOccurrence

/-! Converse copying enabledness uses the actually selected contraction spine.
Unused weakening siblings stay in the original complement, while the payload
is reconstructed with its complete original larger box interface. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.Decoration
open Graph Opening
variable {d I O} {G : Hypernet d I O} (D : Decoration G)

/-- Every actual right copying occurrence yields a real left copying rewrite
at the same projected token; no retained-footprint or matching premise remains. -/
theorem copying_enabled {n k h} (T : ContractionTree .term (n+1))
    (A : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable A)
    (f : Occurrence (CopyRule.before T A) D.graph) :
    ∃ H : Hypernet d I O, ∃ v,
      Combined.Rewrite G (D.project (f.ports (.input ⟨0,by simp⟩))) H v := by
  obtain ⟨m,orientation,small,input,payload,paths⟩ := CopyRule.minimal_occurrence T A ⟨0,by simp⟩
  let U := ContractionSpine.tree .term m orientation
  let actual : Occurrence (CopyRule.before U A) D.graph := small.comp f
  let tree := (ReverseComponents.serialLeft (CopyRule.tree U d) A).comp actual
  let value := (ReverseComponents.serialRight (CopyRule.tree U d) A).comp actual
  have full : ∀ e : (CopyRule.tree U d).Edge, ∃ p,
      (CopyRule.tree U d).edgeLabel e = primitiveLabel d p ∧ ∀ s, p ≠ .weakening s := by
    intro e
    refine ⟨.contraction .term,?_,fun s eq => by cases eq⟩
    cases d <;> rfl
  let reflected := D.reflectPrimitiveOccurrence tree.matchEmbedding full
  obtain ⟨k',h',B,copyB,g,inputs⟩ := reflectCopyable copyable D value
  have boundary : ∀ i, reflected.ports (.output i) = g.ports (.input i) := by
    intro i
    rw [inputs]
    change D.project (actual.ports ((ReverseComponents.serialLeft _ _).ports (.output i))) = _
    rw [ReverseComponents.serial_boundary]
    rfl
  let joint := Occurrence.sharingCopyJoin U reflected g copyB boundary
  have step := joint.local_rewrite (.copy U B copyB)
  have position : joint.ports (.input ⟨0,by simp⟩) =
      D.project (f.ports (.input ⟨0,by simp⟩)) := by
    dsimp only [joint,Occurrence.sharingCopyJoin]
    rw [Occurrence.SerialJoin.occurrence_input]
    change D.project (actual.ports (BoundarySerial.leftInsert _ _ (.input _))) = _
    rw [Combined.left_input]
    change D.project (f.ports (small.ports (.input _))) = _
    rw [input]
  rw [position] at step
  exact ⟨_,_,step⟩
end Hypernets.Copying.BoxPullWeakening.Decoration
