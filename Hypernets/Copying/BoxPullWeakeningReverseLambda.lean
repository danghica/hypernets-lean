import Hypernets.Copying.BoxPullWeakeningReversePrimitive
import Hypernets.Copying.BoxPullWeakeningReverseBox
import Hypernets.Copying.SharingTreeSerialJoin

/-! Converse reconstruction of an actual lambda payload. Its source box keeps
all of its original free ports, including the port weakened only on the right. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Opening
namespace ReverseComponents
noncomputable def serialLeft {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) :
    Occurrence A (Serial.net A B) :=
  (MatchEmbedding.serialLeft A B).occurrence (fun e => by
    change LabelEquiv d _ ((Serial.net A B).edgeLabel (Serial.leftEdge A B e))
    rw [Serial.leftEdge_label]; exact labelEquiv_refl _ _)
noncomputable def serialRight {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) :
    Occurrence B (Serial.net A B) :=
  (MatchEmbedding.serialRight A B).occurrence (fun e => by
    change LabelEquiv d _ ((Serial.net A B).edgeLabel (Serial.rightEdge A B e))
    rw [Serial.rightEdge_label]; exact labelEquiv_refl _ _)

theorem serial_boundary {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) (i : Fin J.length) :
    (serialLeft A B).ports (.output i) = (serialRight A B).ports (.input i) := by
  cases d <;> rfl
end ReverseComponents

namespace Decoration
variable {d I O} {G : Hypernet (d+1) I O} (D : Decoration G)

/-- Every actual right lambda has a complete left copyable lambda occurrence,
with the same incoming token and the unchanged larger original body. -/
theorem reflectLambda {k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (f : Occurrence (lambdaPayload B) D.graph) :
    ∃ k' h', ∃ C : Hypernet d [.term] (environmentInterface (k'+1) h'),
      ∃ g : Occurrence (lambdaPayload C) G,
        ∀ i, g.ports (.input i) = D.project (f.ports (.input i)) := by
  let l := (ReverseComponents.serialLeft (primitiveNet (d+1) (.operation .lam))
    (Translation.lambdaBox B)).comp f
  let b := (ReverseComponents.serialRight (primitiveNet (d+1) (.operation .lam))
    (Translation.lambdaBox B)).comp f
  let q := D.reflectPrimitiveOccurrence l.matchEmbedding (fun _ => ⟨.operation .lam,rfl,by intro s; intro bad; cases bad⟩)
  obtain ⟨k',h',C,g,inputs⟩ := D.reflectBox b
  let C' : Hypernet d [.term] (environmentInterface (k'+1) h') :=
    Translation.castInterfaces rfl (congrArg (fun n => environmentInterface n h') (Nat.add_comm 1 k')) C
  have eq : Translation.lambdaBox C' = box (bound := 1) (freeVariables := k') C := by
    simp only [Translation.lambdaBox,C',BoxPermutation.cast_roundtrip]
  let iso : DeepIso (Translation.lambdaBox C') (box (bound := 1) (freeVariables := k') C) := by
    rw [eq]; exact DeepIso.refl _
  let g' : Occurrence (Translation.lambdaBox C') G := (Occurrence.ofIso iso).comp g
  have inputEq : ∀ i, g'.ports (.input i) = D.project (b.ports (.input i)) := by
    exact inputs
  have boundary : ∀ i, q.ports (.output i) = g'.ports (.input i) := by
    intro i
    rw [inputEq]
    change D.project (f.ports ((ReverseComponents.serialLeft _ _).ports (.output i))) = _
    rw [ReverseComponents.serial_boundary]
    rfl
  have disjoint : ∀ e a, q.edges e ≠ g'.edges a := by
    intro e a same
    have lam := q.matchEmbedding.primitive e (.operation .lam) rfl
    change G.edgeLabel (q.edges e) = _ at lam
    have box := g'.label a
    rw [← same,lam] at box
    exact box
  let result := Occurrence.SerialJoin.occurrence q g' boundary disjoint
  refine ⟨k',h',C',result,?_⟩
  intro i
  rw [Occurrence.SerialJoin.occurrence_input]
  change D.project (f.ports (BoundarySerial.leftInsert _ _ (.input i))) = _
  rw [Combined.left_input]
end Decoration
end Hypernets.Copying.BoxPullWeakening
