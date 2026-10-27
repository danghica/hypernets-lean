import Hypernets.Copying.CopySuccessorIncidences

/-! The full original copying reduct realizes its source-relative presentation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening
variable {d n k h} (T : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (normal : NormalForm H)

theorem local_tail_eq : (localSuccessorMatch T normal).tail = Serial.rightEdge (tree T d) H normal.tail := by cases d <;> rfl

theorem local_active_not_payload (e : H.Edge) : Serial.rightEdge (tree T d) H e ≠ (localSuccessorMatch T normal).active := by
  intro eq
  have label := (Serial.rightEdge_label (tree T d) H e).symm.trans
    ((congrArg (before T H).edgeLabel eq).trans (localSuccessorMatch T normal).active_label)
  have allowed := normal.copyable.outer_labels e
  cases d <;> simpa [label,Copyable.OuterLabel,primitiveLabel] using allowed

theorem local_source (e : (before T H).Edge ⊕ AddedEdge H) :
    ((after T H).source (successorEdgeInverse T H e)).map (Port.map (successorVertices T H)) =
      (localSuccessorMatch T normal).presentation.source e := by
  classical
  cases d
  all_goals
    rcases e with ⟨b,e⟩ | (e | (e | e))
    · cases b
      · change ((after T H).source (keptTreeEdge T H e)).map _ = _
        rw [kept_tree_source,List.map_map]
        calc
          _ = ((T.net.source e).map (BoundarySerial.leftInsert (tree T _) H)).map
              (divertedPort (H := H) (.input ⟨0,by simp⟩)) := by
            rw [List.map_map]; exact List.map_congr_left (fun p _ => tree_port T H p)
          _ = _ := (localSuccessorMatch T normal).source_divert (Serial.leftEdge (tree T _) H e)
      · change ((after T H).source (rightEdge T H e)).map _ = _
        rw [retained_source,List.map_map]
        simp only [SuccessorMatch.presentation]
        have ne : (⟨true,e⟩ : (before T H).Edge) ≠ (localSuccessorMatch T normal).active := local_active_not_payload T normal e
        rw [ite_eq_right ne]
        change _ = ((H.source e).map (BoundarySerial.rightInsert (tree T _) H)).map _
        rw [List.map_map]
        apply List.map_congr_left
        intro p hp
        cases p with
        | internal x => exact retained_internal T H x
        | input i => exact retained_input T H i
        | output i => exact False.elim (H.source_not_output hp trivial)
    · change ((after T H).source (leftEdge T H e)).map _ = _
      rw [active_source,List.map_map]
      exact List.map_congr_left (fun p _ => active_port T H p)
    · have eq : e = 0 := by apply Fin.ext; omega
      subst e
      change ((after T H).source (addedWeakening T H)).map _ = []
      rw [added_weakening_source]; rfl
    · change (((Translation.environmentDistributor _ k h 2).source e).map
        (BoundarySerial.rightInsert (copies T H) (Translation.environmentDistributor _ k h 2))).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun p _ => distributor_port T normal p)

theorem local_target (e : (before T H).Edge ⊕ AddedEdge H) :
    ((after T H).target (successorEdgeInverse T H e)).map (Port.map (successorVertices T H)) =
      (localSuccessorMatch T normal).presentation.target e := by
  classical
  cases d
  all_goals
    rcases e with ⟨b,e⟩ | (e | (e | e))
    · cases b
      · change ((after T H).target (keptTreeEdge T H e)).map _ = _
        rw [kept_tree_target,List.map_map]
        have endEq : (localSuccessorMatch T normal).tail = (⟨true,normal.tail⟩ : (before T H).Edge) := local_tail_eq T normal
        have ne : (⟨false,e⟩ : (before T H).Edge) ≠ (localSuccessorMatch T normal).tail := by
          rw [endEq]; intro eq; have bad := congrArg Sigma.fst eq; cases bad
        simp only [SuccessorMatch.presentation]
        rw [ite_eq_right ne]
        change _ = ((T.net.target e).map (BoundarySerial.leftInsert (tree T _) H)).map _
        rw [List.map_map]
        apply List.map_congr_left
        intro p hp
        cases p with
        | internal x => exact tree_internal T H x
        | input i => exact False.elim (T.net.target_not_input hp trivial)
        | output i => exact tree_output T H i
      · change ((after T H).target (rightEdge T H e)).map _ = _
        rw [retained_target,List.map_map]
        simp only [SuccessorMatch.presentation]
        have endEq : (localSuccessorMatch T normal).tail = (⟨true,normal.tail⟩ : (before T H).Edge) := local_tail_eq T normal
        rw [endEq]
        by_cases eq : e = normal.tail
        · subst e
          rw [ite_eq_left rfl,normal.tail_target,List.map_map]
          exact List.map_congr_left (fun i _ => retained_output T H i)
        · have ne : (⟨true,e⟩ : (before T H).Edge) ≠ ⟨true,normal.tail⟩ :=
            fun same => eq (eq_of_heq (Sigma.mk.inj same).2)
          rw [ite_eq_right ne]
          change _ = ((H.target e).map (BoundarySerial.rightInsert (tree T _) H)).map _
          rw [List.map_map]
          apply List.map_congr_left
          intro p hp
          obtain ⟨x,rfl⟩ := normal.nonTail_targets_internal eq hp
          exact retained_internal T H x
    · change ((after T H).target (leftEdge T H e)).map _ = _
      rw [active_target,List.map_map]
      exact List.map_congr_left (fun p _ => active_port T H p)
    · have eq : e = 0 := by apply Fin.ext; omega
      subst e
      change ((after T H).target (addedWeakening T H)).map _ = [SuccessorMatch.weakPort]
      rw [added_weakening_target,List.map_cons,List.map_nil,tree_zero]
    · change (((Translation.environmentDistributor _ k h 2).target e).map
        (BoundarySerial.rightInsert (copies T H) (Translation.environmentDistributor _ k h 2))).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun p _ => distributor_port T normal p)

noncomputable def localRealization : Opening.Realization (localSuccessorMatch T normal).presentation (after T H) where
  vertices := successorVertices T H
  edges := successorEdges T H
  vertex_injective := fun _ _ h => (successorVertexBijection T H).injective h
  edge_injective := fun _ _ h => (successorEdgeBijection T H).injective h
  vertex_range x := ⟨fun _ => trivial,fun _ => ⟨successorVertexInverse T H x,(successorVertexBijection T H).right_inv x⟩⟩
  edge_range e := ⟨fun _ => trivial,fun _ => ⟨successorEdgeInverse T H e,(successorEdgeBijection T H).right_inv e⟩⟩
  internal_label := by
    intro x
    have check (y : (before T H).Internal ⊕ AddedVertex H) :
        (after T H).internalLabel (successorVertexInverse T H y) = (localSuccessorMatch T normal).presentation.vertexLabel y := by
      cases d
      all_goals
        rcases y with (y | ⟨b,y⟩) | (y | (y | (y | y)))
        · rfl
        · cases b <;> rfl
        · rfl
        · rfl
        · rfl
        · rfl
    have eq := check (successorVertices T H x)
    rw [show successorVertexInverse T H (successorVertices T H x) = x from (successorVertexBijection T H).left_inv x] at eq
    exact eq
  edge_label := by
    intro e
    have check (y : (before T H).Edge ⊕ AddedEdge H) :
        (after T H).edgeLabel (successorEdgeInverse T H y) = (localSuccessorMatch T normal).presentation.edgeLabel y := by
      cases d
      all_goals
        rcases y with ⟨b,y⟩ | (y | (y | y))
        · cases b <;> rfl
        · rfl
        · rfl
        · rfl
    have eq := check (successorEdges T H e)
    rw [show successorEdgeInverse T H (successorEdges T H e) = e from (successorEdgeBijection T H).left_inv e] at eq
    rw [eq]; exact labelEquiv_refl _ _
  source e := by
    have eq := local_source T normal (successorEdges T H e)
    rw [show successorEdgeInverse T H (successorEdges T H e) = e from (successorEdgeBijection T H).left_inv e] at eq
    exact eq
  target e := by
    have eq := local_target T normal (successorEdges T H e)
    rw [show successorEdgeInverse T H (successorEdges T H e) = e from (successorEdgeBijection T H).left_inv e] at eq
    exact eq

noncomputable def local_certificate : SuccessorCertificate (before T H) (after T H)
    (.input ⟨0,by simp⟩) (.input ⟨0,by simp⟩) H where
  matched := localSuccessorMatch T normal
  realization := localRealization T normal
  token := rfl
end Hypernets.Copying.CopyRule
