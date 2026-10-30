import Hypernets.Copying.BoxPullContractionCoordinates
import Hypernets.Copying.ExpansionOccurrenceJoin

/-! Join an actual graph occurrence to an actual output contraction, using
only their exact ordered junctions and edge disjointness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence.MergeJoin
open Graph BoxPullContraction
variable {d I A B X Y} {s : ShareSort}
    {G : Hypernet d I (A ++ s.wire :: s.wire :: B)} {H : Hypernet d X Y}
    (f : Occurrence G H) (g : Occurrence (primitiveNet d (.contraction s)) H)

def host : Port (Fin 2) I.length (A ++ s.wire :: B).length → H.Vertex
  | .internal i => g.ports (.input i)
  | .input i => f.ports (.input i)
  | .output i =>
    if before : i.val < A.length then f.ports (.output ⟨i.val,by simp; omega⟩)
    else if selected : i.val = A.length then g.ports (.output ⟨0,by change 0 < 1; decide⟩)
    else f.ports (.output ⟨i.val+1,by have := i.isLt; simp at this ⊢; omega⟩)

noncomputable def components : ∀ b, Occurrence (filling s G b) H := by
  cases d <;> intro b <;> cases b
  all_goals first | exact f | exact g

variable (join : ∀ i : Fin 2,
    f.ports (.output ⟨A.length+i.val,by have := i.isLt; simp; omega⟩) = g.ports (.input i))
include join

theorem component_input (b) (i) :
    (components f g b).ports (.input i) = host f g ((pattern d I A B s).sourcePort b i) := by
  cases d <;> cases b
  all_goals first
    | (change Fin I.length at i
       change f.ports (.input i) = host f g ((frame I A B s).sourcePort false i)
       simp [host,Net.sourcePort,frame,frameSource,List.getElem_map,List.getElem_finRange])
    | (change Fin 2 at i
       have cases : i = 0 ∨ i = 1 := by
         have bound := i.isLt
         by_cases z : i.val = 0
         · exact .inl (Fin.ext z)
         · exact .inr (Fin.ext (by omega))
       rcases cases with rfl | rfl
       all_goals rfl)

theorem old_output (i : Fin (A ++ s.wire :: s.wire :: B).length) :
    f.ports (.output i) = host f g ((frame I A B s).targetPort false i) := by
  rw [frame_targetPort]
  by_cases before : i.val < A.length
  · simp only [before,↓reduceDIte,host]
  · by_cases middle : i.val < A.length+2
    · simp only [before,middle,↓reduceDIte,host]
      have eq := join ⟨i.val-A.length,by omega⟩
      have index : (⟨A.length+(i.val-A.length),by have := i.isLt; simp at this ⊢; omega⟩ :
          Fin (A ++ s.wire :: s.wire :: B).length) = i := Fin.ext (by change A.length+(i.val-A.length) = i.val; omega)
      simpa only [index] using eq
    · simp only [before,middle,↓reduceDIte,host]
      have before' : ¬ i.val-1 < A.length := by omega
      have selected' : ¬ i.val-1 = A.length := by omega
      simp only [before',selected',↓reduceDIte]
      apply congrArg f.ports
      apply congrArg Port.output
      apply Fin.ext
      dsimp
      omega

theorem component_output (b) (i) :
    (components f g b).ports (.output i) = host f g ((pattern d I A B s).targetPort b i) := by
  cases d <;> cases b
  all_goals first
    | exact old_output f g join i
    | (change Fin 1 at i
       have index : i = ⟨0,by decide⟩ := Subsingleton.elim _ _
       subst i
       change g.ports (.output ⟨0,by change 0 < 1; decide⟩) = host f g (selectedPort I A B s)
       simp [host,selectedPort])

/-- The resulting complete occurrence contains every original edge of G and
the actual external contraction. All internal freshness follows from incidence. -/
noncomputable def occurrence (disjoint : ∀ e a, f.edges e ≠ g.edges a) :
    Occurrence (merge s G) H :=
  Occurrence.ExpansionJoin.occurrence (pattern d I A B s) (filling s G)
    (components f g) (host f g)
    (component_input f g join) (component_output f g join) (by
      cases d <;> intro b c ne e a
      all_goals cases b <;> cases c
      all_goals first | exact False.elim (ne rfl) | exact disjoint e a | exact fun eq => disjoint a e eq.symm)

variable (disjoint : ∀ e a, f.edges e ≠ g.edges a)

theorem occurrence_input (i : Fin I.length) :
    (occurrence f g join disjoint).ports (.input i) = f.ports (.input i) := rfl

theorem occurrence_output (i : Fin (A ++ s.wire :: B).length) :
    (occurrence f g join disjoint).ports (.output i) = host f g (.output i) := rfl

theorem occurrence_old (v : G.Vertex) :
    (occurrence f g join disjoint).ports (oldPort s G v) = f.ports v := by
  rw [← oldPort_insert s G v]
  unfold occurrence
  cases d
  all_goals exact Occurrence.ExpansionJoin.occurrence_insert (pattern _ I A B s) (filling s G) _ _ _ _ _ false v

theorem occurrence_oldEdge (e : G.Edge) :
    (occurrence f g join disjoint).edges (oldEdge s G e) = f.edges e := by cases d <;> rfl

theorem occurrence_contractionEdge :
    (occurrence f g join disjoint).edges (contractionEdge s G) = g.edges (by cases d <;> exact (0 : Fin 1)) := by cases d <;> rfl

end Hypernets.Copying.Opening.Occurrence.MergeJoin
