import Hypernets.Copying.BoxPullContractionLaws
import Hypernets.Copying.SpliceBoundary

/-! Explicit ordered coordinates for the single contraction attached to an
output pair. These identify actual beta residuals without changing the body. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

def junction {d I A B} (s : ShareSort) (G : Hypernet d I (A ++ s.wire :: s.wire :: B))
    (i : Fin 2) : (merge s G).Vertex := .internal (.inl i)

/-- Only the selected pair of old outputs becomes internal. All other old
ports retain their original order, with one output removed from the list. -/
def oldPort {d I A B} (s : ShareSort) (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) :
    G.Vertex → (merge s G).Vertex
  | .internal v => .internal (.inr ⟨false,by cases d <;> exact v⟩)
  | .input i => .input i
  | .output i =>
      if before : i.val < A.length then .output ⟨i.val,by simp; omega⟩
      else if middle : i.val < A.length+2 then junction s G ⟨i.val-A.length,by omega⟩
      else .output ⟨i.val-1,by have bound := i.isLt; simp at bound ⊢; omega⟩

theorem frame_targetPort {I A B} (s : ShareSort)
    (i : Fin (A ++ s.wire :: s.wire :: B).length) :
    (frame I A B s).targetPort false i =
      if before : i.val < A.length then .output ⟨i.val,by simp; omega⟩
      else if middle : i.val < A.length+2 then .internal ⟨i.val-A.length,by omega⟩
      else .output ⟨i.val-1,by have bound := i.isLt; simp at bound ⊢; omega⟩ := by
  change (prefixPorts I A B s ++ .internal 0 :: .internal 1 :: suffixPorts I A B s)[i.val]'(by
    have bound := i.isLt
    simpa [prefixPorts,suffixPorts] using bound) = _
  by_cases before : i.val < A.length
  · rw [dite_eq_left before,List.getElem_append_left (by simpa [prefixPorts] using before)]
    simp [prefixPorts,List.getElem_map,prefixPort]
  · rw [dite_eq_right before,List.getElem_append_right (by simp [prefixPorts]; omega)]
    by_cases middle : i.val < A.length+2
    · rw [dite_eq_left middle]
      have cases : i.val-A.length = 0 ∨ i.val-A.length = 1 := by omega
      rcases cases with h | h
      all_goals
        simp only [prefixPorts,List.length_map,List.length_finRange,h]
        apply congrArg Port.internal
        apply Fin.ext
        simp only [Fin.val_zero,Fin.val_one]
    · rw [dite_eq_right middle]
      have bound : 2 ≤ i.val-A.length := by omega
      simp only [prefixPorts,List.length_map,List.length_finRange]
      rw [List.getElem_cons,dite_eq_right (by omega),List.getElem_cons,dite_eq_right (by omega)]
      simp only [suffixPorts,List.getElem_map,List.getElem_finRange,suffixPort]
      apply congrArg Port.output
      apply Fin.ext
      dsimp
      omega

/-- The explicit old-port map is the actual simultaneous-expansion
embedding, including both internalized output coordinates. -/
theorem oldPort_insert {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) (v : G.Vertex) :
    Net.Expansion.insert (pattern d I A B s) (filling s G) false
      (show (filling s G false).Vertex from by cases d <;> exact v) = oldPort s G v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i =>
    cases d
    all_goals
      simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,pattern,frame,frameSource,
        List.getElem_map,oldPort,Port.map]
  | output i =>
    cases d
    all_goals
      change Port.map Sum.inl ((frame I A B s).targetPort false i) = _
      rw [frame_targetPort]
      by_cases before : i.val < A.length
      · simp [oldPort,before,Port.map]
      · by_cases middle : i.val < A.length+2
        all_goals simp [oldPort,before,middle,junction,Port.map]

@[reducible] def oldEdge {d I A B} (s : ShareSort) (G : Hypernet d I (A ++ s.wire :: s.wire :: B))
    (e : G.Edge) : (merge s G).Edge := ⟨false,by cases d <;> exact e⟩

@[reducible] def contractionEdge {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) : (merge s G).Edge :=
  ⟨true,by cases d <;> exact (0 : Fin 1)⟩

theorem merge_source {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) (e : G.Edge) :
    (merge s G).source (oldEdge s G e) = (G.source e).map (oldPort s G) := by
  cases d
  all_goals exact List.map_congr_left (fun v _ => oldPort_insert s G v)

theorem merge_target {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) (e : G.Edge) :
    (merge s G).target (oldEdge s G e) = (G.target e).map (oldPort s G) := by
  cases d
  all_goals exact List.map_congr_left (fun v _ => oldPort_insert s G v)

theorem merge_contraction_source {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) :
    (merge s G).source (contractionEdge s G) = [junction s G 0,junction s G 1] := by
  cases d <;> rfl

theorem merge_contraction_target {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) :
    (merge s G).target (contractionEdge s G) = [.output ⟨A.length,by simp⟩] := by
  cases d <;> rfl

end Hypernets.Copying.BoxPullContraction
