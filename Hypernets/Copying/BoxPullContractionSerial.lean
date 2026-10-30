import Hypernets.Copying.BoxPullContractionCoordinates
import Hypernets.Copying.BoundarySerial

/-! Attaching a contraction to an output pair commutes with an unchanged
serial prefix. This preserves every original port and recursive edge label. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.SerialPull
open Graph
variable {d : Nat} {I J A B : List Wire}
  (s : ShareSort) (P : Hypernet d I J)
  (G : Hypernet d J (A ++ s.wire :: s.wire :: B))

abbrev left := Serial.net P (merge s G)
abbrev right := merge s (Serial.net P G)

def vertices : Bijection (left s P G).Internal (right s P G).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => .inr ⟨false,.inl j⟩
      | .inr ⟨false,v⟩ => .inr ⟨false,.inr ⟨false,v⟩⟩
      | .inr ⟨true,.inl j⟩ => .inl j
      | .inr ⟨true,.inr ⟨false,v⟩⟩ => .inr ⟨false,.inr ⟨true,v⟩⟩
      | .inr ⟨true,.inr ⟨true,v⟩⟩ => nomatch v
    invFun := fun
      | .inl j => .inr ⟨true,.inl j⟩
      | .inr ⟨false,.inl j⟩ => .inl j
      | .inr ⟨false,.inr ⟨false,v⟩⟩ => .inr ⟨false,v⟩
      | .inr ⟨false,.inr ⟨true,v⟩⟩ => .inr ⟨true,.inr ⟨false,v⟩⟩
      | .inr ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rfl
        · rcases v with j | ⟨b,v⟩; rfl; cases b; rfl; exact nomatch v
    right_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl
        · exact nomatch v }

def edges : Bijection (left s P G).Edge (right s P G).Edge := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,e⟩ => ⟨false,⟨false,e⟩⟩
      | ⟨true,⟨false,e⟩⟩ => ⟨false,⟨true,e⟩⟩
      | ⟨true,⟨true,e⟩⟩ => ⟨true,e⟩
    invFun := fun
      | ⟨false,⟨false,e⟩⟩ => ⟨false,e⟩
      | ⟨false,⟨true,e⟩⟩ => ⟨true,⟨false,e⟩⟩
      | ⟨true,e⟩ => ⟨true,⟨true,e⟩⟩
    left_inv := by rintro ⟨b,e⟩; cases b; rfl; rcases e with ⟨b,e⟩; cases b <;> rfl
    right_inv := by rintro ⟨b,e⟩; cases b; rcases e with ⟨b,e⟩; cases b <;> rfl; rfl }

theorem prefix_commutes (v : P.Vertex) :
    Port.map (vertices s P G).toFun (BoundarySerial.leftInsert P (merge s G) v) =
      oldPort s (Serial.net P G) (BoundarySerial.leftInsert P G v) := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).sourcePort false i)) =
      oldPort s (Serial.net P G) (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: s.wire :: B)).sourcePort false i))
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl
  | output i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).targetPort false i)) =
      oldPort s (Serial.net P G) (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: s.wire :: B)).targetPort false i))
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

private theorem suffix_output {d I J O} (P : Hypernet d I J)
    (G : Hypernet d J O) (i : Fin O.length) :
    BoundarySerial.rightInsert P G (.output i) = .output i := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort true i) = _
    simp [Net.targetPort,Serial.pattern,List.getElem_map,Port.map]

theorem suffix_commutes (v : G.Vertex) :
    Port.map (vertices s P G).toFun
      (BoundarySerial.rightInsert P (merge s G) (oldPort s G v)) =
      oldPort s (Serial.net P G) (BoundarySerial.rightInsert P G v) := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).sourcePort true i)) =
      oldPort s (Serial.net P G) (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: s.wire :: B)).sourcePort true i))
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl
  | output i =>
    rw [suffix_output]
    by_cases before : i.val < A.length
    · simp only [oldPort,dite_eq_left before,suffix_output]
      rfl
    · by_cases middle : i.val < A.length+2
      · simp only [oldPort,dite_eq_right before,dite_eq_left middle]
        rfl
      · simp only [oldPort,dite_eq_right before,dite_eq_right middle,suffix_output]
        rfl

def prefixEdge (e : P.Edge) : (left s P G).Edge := by cases d <;> exact ⟨false,e⟩
def suffixEdge (e : G.Edge) : (left s P G).Edge := by cases d <;> exact ⟨true,⟨false,e⟩⟩
def contraction (e : (primitiveNet d (.contraction s)).Edge) : (left s P G).Edge := by
  cases d <;> exact ⟨true,⟨true,e⟩⟩

theorem edge_cases (e : (left s P G).Edge) :
    (∃ p, e = prefixEdge s P G p) ∨ (∃ g, e = suffixEdge s P G g) ∨
      (∃ w, e = contraction s P G w) := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | exact .inl ⟨e,rfl⟩
    | (rcases e with ⟨b,e⟩; cases b
       · exact .inr (.inl ⟨e,rfl⟩)
       · exact .inr (.inr ⟨e,rfl⟩))

def iso : DeepIso (left s P G) (right s P G) where
  vertices := vertices s P G
  edges := edges s P G
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | rfl
      | (cases b; rfl; rcases v with j | ⟨b,v⟩; rfl; cases b; rfl; exact nomatch v)
  edge_label e := by
    rcases edge_cases s P G e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    all_goals cases d <;> exact labelEquiv_refl _ _
  source e := by
    rcases edge_cases s P G e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · cases d
      all_goals
        change ((P.source e).map (BoundarySerial.leftInsert P (merge s G))).map _ =
          (merge s (Serial.net P G)).source ⟨false,⟨false,e⟩⟩
        refine Eq.trans ?_ (merge_source s (Serial.net P G) _).symm
        change ((P.source e).map _).map _ = ((P.source e).map _).map _
        rw [List.map_map,List.map_map]
        exact List.map_congr_left (fun v _ => prefix_commutes s P G v)
    · cases d
      all_goals
        change (((merge s G).source ⟨false,e⟩).map _).map _ =
          (merge s (Serial.net P G)).source ⟨false,⟨true,e⟩⟩
        refine (congrArg (fun l => (l.map (BoundarySerial.rightInsert P (merge s G))).map (Port.map (vertices s P G).toFun)) (merge_source s G e)).trans ?_
        refine Eq.trans ?_ (merge_source s (Serial.net P G) _).symm
        change (((G.source e).map _).map _).map _ = ((G.source e).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => suffix_commutes s P G v)
    · cases d
      all_goals
        change Fin 1 at e
        have he : e = 0 := Fin.ext (by omega)
        subst e
        rfl
  target e := by
    rcases edge_cases s P G e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · cases d
      all_goals
        change ((P.target e).map (BoundarySerial.leftInsert P (merge s G))).map _ =
          (merge s (Serial.net P G)).target ⟨false,⟨false,e⟩⟩
        refine Eq.trans ?_ (merge_target s (Serial.net P G) _).symm
        change ((P.target e).map _).map _ = ((P.target e).map _).map _
        rw [List.map_map,List.map_map]
        exact List.map_congr_left (fun v _ => prefix_commutes s P G v)
    · cases d
      all_goals
        change (((merge s G).target ⟨false,e⟩).map _).map _ =
          (merge s (Serial.net P G)).target ⟨false,⟨true,e⟩⟩
        refine (congrArg (fun l => (l.map (BoundarySerial.rightInsert P (merge s G))).map (Port.map (vertices s P G).toFun)) (merge_target s G e)).trans ?_
        refine Eq.trans ?_ (merge_target s (Serial.net P G) _).symm
        change (((G.target e).map _).map _).map _ = ((G.target e).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => suffix_commutes s P G v)
    · cases d
      all_goals
        change Fin 1 at e
        have he : e = 0 := Fin.ext (by omega)
        subst e
        change [Port.map _ (BoundarySerial.rightInsert P (merge s G)
          (.output ⟨A.length,by simp⟩))] = [.output ⟨A.length,by simp⟩]
        rw [suffix_output]
        rfl

end Hypernets.Copying.BoxPullContraction.SerialPull
