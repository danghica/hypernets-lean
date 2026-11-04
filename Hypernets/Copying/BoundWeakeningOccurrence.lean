import Hypernets.Copying.BoxPullWeakeningParallelJoin
import Hypernets.Copying.BoxPullWeakeningCoordinates
import Hypernets.Copying.BoundarySourceReboundary

/-! Complete occurrences of an ignored-bound-variable body assemble from
its original component and an actual disjoint weakening edge. The bound
output remains exposed to the original surrounding argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.AdjoinOccurrence
open Graph Opening
private theorem cast_cancel {α : Type} {I O J K : List Wire} (hi : I=J) (ho : O=K)
    (v : Port α I.length O.length) : Port.cast hi.symm ho.symm (Port.cast hi ho v) = v := by
  cases hi; cases ho; cases v <;> rfl

variable {d I A B J K} (R : Hypernet d I (A++B)) (s : ShareSort)
    {H : Hypernet d J K} (f : Occurrence R H)
    (g : Occurrence (primitiveNet d (.weakening s)) H)
    (apart : ∀ e w, f.edges e ≠ g.edges w)

noncomputable def components (b : Bool) :
    Occurrence (Net.Tensor.family R (primitiveNet d (.weakening s)) b) H := by
  cases b
  · exact f
  · exact g

noncomputable def inserted : Occurrence (insert R s) H :=
  Occurrence.ParallelJoin.occurrence _ (insertionBoundary I A B s)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (components R s f g) (by
      intro a b ne e w
      cases a <;> cases b
      · exact False.elim (ne rfl)
      · exact apart e w
      · exact fun eq => apart w e eq.symm
      · exact False.elim (ne rfl))

noncomputable def occurrence : Occurrence (adjoin R s) H :=
  (inserted R s f g apart).reboundarySource (List.append_nil I)
    (by simp only [List.append_nil,List.append_assoc,List.singleton_append])

theorem old (v : R.Vertex) :
    (occurrence R s f g apart).ports (oldPort R s v) = f.ports v := by
  rw [← oldPort_insert]
  change (inserted R s f g apart).ports
    (Port.cast (List.append_nil I).symm
      (show (A++[s.wire])++(B++[]) = A++s.wire::B by simp only [List.append_nil,List.append_assoc,List.singleton_append]).symm
      (Port.cast (List.append_nil I)
      (show (A++[s.wire])++(B++[]) = A++s.wire::B by simp only [List.append_nil,List.append_assoc,List.singleton_append])
      (Net.Parallel.embed _ (insertionBoundary I A B s) false v))) = _
  rw [cast_cancel]
  exact Occurrence.ParallelJoin.occurrence_embed (Net.Tensor.family R (primitiveNet d (.weakening s))) (insertionBoundary I A B s) _ (components R s f g) _ false v

theorem input (i : Fin I.length) :
    (occurrence R s f g apart).ports (.input i) = f.ports (.input i) :=
  old R s f g apart (.input i)

theorem weakening :
    (occurrence R s f g apart).ports (.output (weakeningOutput A B s)) =
      g.ports (.output ⟨0,by change 0 < 1; omega⟩) := by
  have represented : Port.cast (List.append_nil I)
      (show (A++[s.wire])++(B++[]) = A++s.wire::B by
        simp only [List.append_nil,List.append_assoc,List.singleton_append])
      (Net.Parallel.embed (Net.Tensor.family R (primitiveNet d (.weakening s)))
        (insertionBoundary I A B s) true (.output ⟨0,by change 0 < 1; omega⟩)) =
      .output (weakeningOutput A B s) := by
    apply congrArg Port.output
    exact Fin.ext (inserted_weakening_output s)
  rw [← represented]
  change (inserted R s f g apart).ports
    (Port.cast (List.append_nil I).symm
      (show (A++[s.wire])++(B++[]) = A++s.wire::B by simp only [List.append_nil,List.append_assoc,List.singleton_append]).symm
      (Port.cast (List.append_nil I)
      (show (A++[s.wire])++(B++[]) = A++s.wire::B by simp only [List.append_nil,List.append_assoc,List.singleton_append])
      (Net.Parallel.embed _ (insertionBoundary I A B s) true (.output ⟨0,_⟩)))) = _
  rw [cast_cancel]
  exact Occurrence.ParallelJoin.occurrence_embed (Net.Tensor.family R (primitiveNet d (.weakening s))) (insertionBoundary I A B s) _ (components R s f g) _ true (.output ⟨0,_⟩)
end Hypernets.Copying.BoxPullWeakening.AdjoinOccurrence
