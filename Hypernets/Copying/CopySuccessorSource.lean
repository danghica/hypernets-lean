import Hypernets.Copying.CopySuccessorPorts

/-! The residual tree changes only the selected source attachment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening

noncomputable def divertedPort {d I O k h} {G : Hypernet d I O}
    {H : Hypernet d [.term] (environmentInterface k h)} (v p : G.Vertex) :
    Port (G.Internal ⊕ AddedVertex H) I.length O.length := by
  classical
  exact if p = v then SuccessorMatch.weakPort else Port.map Sum.inl p

theorem SuccessorMatch.source_divert {d I O k h} {G : Hypernet d I O} {v}
    {H : Hypernet d [.term] (environmentInterface k h)} (a : SuccessorMatch G v H) (e : G.Edge) :
    (G.source e).map (divertedPort (H := H) v) = a.presentation.source (.inl e) := by
  classical
  by_cases eq : e = a.active
  · subst e
    change _ = if _ then _ else _
    rw [ite_eq_left rfl,a.active_source]
    have ne := a.distinct
    cases hr : a.right <;> simp [selectedSources,hr,divertedPort,ne,ne.symm]
  · change _ = if _ then _ else _
    rw [ite_eq_right eq]
    apply List.map_congr_left
    intro p mem
    have ne : p ≠ v := by intro same; subst p; exact eq (G.source_unique mem a.head_at.2)
    simp [divertedPort,ne]

theorem tree_port {d n k h} (T : ContractionTree .term (n+1)) (H : Hypernet d [.term] (environmentInterface k h))
    (p : T.net.Vertex) : Port.map (successorVertices T H) (treeInsert T H p) =
      divertedPort (H := H) (.input ⟨0,by simp⟩) (BoundarySerial.leftInsert (tree T d) H p) := by
  classical
  cases p with
  | internal x =>
    rw [tree_internal]
    cases d
    all_goals
      change Port.internal (.inl (.inr ⟨false,x⟩)) = divertedPort (G := before T H) (H := H) (.input ⟨0,by simp⟩) (.internal (.inr ⟨false,x⟩))
      simp [divertedPort,Port.map]
  | output i => rw [tree_output,serial_left_output]; simp [divertedPort]
  | input i =>
    obtain ⟨i,hi⟩ := i
    cases i with
    | zero => rw [tree_zero,Combined.left_input]; simp [divertedPort]
    | succ i =>
      have bound : i < n := by simpa using hi
      rw [tree_succ T H ⟨i,bound⟩,Combined.left_input]
      simp [divertedPort]

theorem local_tail_targets {d n k h} (T : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (normal : NormalForm H) :
    (before T H).target (localSuccessorMatch T normal).tail =
      (List.finRange (environmentInterface k h).length).map Port.output := by
  cases d
  all_goals
    change (H.target normal.tail).map (BoundarySerial.rightInsert (tree T _) H) = _
    rw [normal.tail_target,List.map_map]
    exact List.map_congr_left (fun i _ => Application.right_serial_output _ _ i)

theorem distributor_port {d n k h} (T : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (normal : NormalForm H)
    (p : (Translation.environmentDistributor d k h 2).Vertex) :
    Port.map (successorVertices T H) (BoundarySerial.rightInsert (copies T H) (Translation.environmentDistributor d k h 2) p) =
      (localSuccessorMatch T normal).distributorPort p := by
  cases p with
  | internal x => cases d <;> rfl
  | input i => rw [serial_right_input]; cases d <;> rfl
  | output i =>
    rw [Application.right_serial_output]
    unfold SuccessorMatch.distributorPort
    simp only [local_tail_targets,List.getElem_map,List.getElem_finRange,Port.map]
    exact congrArg Port.output (Fin.ext rfl)
end Hypernets.Copying.CopyRule
