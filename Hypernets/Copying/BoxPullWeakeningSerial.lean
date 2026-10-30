import Hypernets.Copying.BoxPullWeakeningCoordinates
import Hypernets.Copying.BoundarySerial

/-! Moving a disconnected output weakening past an unchanged serial prefix.
This is graph geometry used to expose the original beta redex on BPullW's
outside-box side, not an additional machine rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.SerialPull
open Graph
variable {d : Nat} {I J A B : List Wire}
  (P : Hypernet d I J) (G : Hypernet d J (A ++ B)) (s : ShareSort)

abbrev left := Serial.net P (adjoin G s)
abbrev right := adjoin (Serial.net P G) s

def vertices : Bijection (left P G s).Internal (right P G s).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => ⟨false,.inl j⟩
      | .inr ⟨false,v⟩ => ⟨false,.inr ⟨false,v⟩⟩
      | .inr ⟨true,⟨false,v⟩⟩ => ⟨false,.inr ⟨true,v⟩⟩
      | .inr ⟨true,⟨true,v⟩⟩ => nomatch v
    invFun := fun
      | ⟨false,.inl j⟩ => .inl j
      | ⟨false,.inr ⟨false,v⟩⟩ => .inr ⟨false,v⟩
      | ⟨false,.inr ⟨true,v⟩⟩ => .inr ⟨true,⟨false,v⟩⟩
      | ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rfl
        · rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v
    right_inv := by
      rintro ⟨b,v⟩
      cases b
      · rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl
      · exact nomatch v }

def edges : Bijection (left P G s).Edge (right P G s).Edge := by
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
    Port.map (vertices P G s).toFun (BoundarySerial.leftInsert P (adjoin G s) v) =
      oldPort (Serial.net P G) s (BoundarySerial.leftInsert P G v) := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).sourcePort false i)) =
      oldPort (Serial.net P G) s (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ B)).sourcePort false i))
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl
  | output i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).targetPort false i)) =
      oldPort (Serial.net P G) s (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ B)).targetPort false i))
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

theorem suffix_commutes (v : G.Vertex) :
    Port.map (vertices P G s).toFun
      (BoundarySerial.rightInsert P (adjoin G s) (oldPort G s v)) =
      oldPort (Serial.net P G) s (BoundarySerial.rightInsert P G v) := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).sourcePort true i)) =
      oldPort (Serial.net P G) s (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ B)).sourcePort true i))
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl
  | output i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).targetPort true (oldOutput A B s i))) =
      oldPort (Serial.net P G) s (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ B)).targetPort true i))
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

def prefixEdge (e : P.Edge) : (left P G s).Edge := by cases d <;> exact ⟨false,e⟩
def suffixEdge (e : G.Edge) : (left P G s).Edge := by cases d <;> exact ⟨true,⟨false,e⟩⟩
def weakEdge (e : (primitiveNet d (.weakening s)).Edge) : (left P G s).Edge := by
  cases d <;> exact ⟨true,⟨true,e⟩⟩

theorem edge_cases (e : (left P G s).Edge) :
    (∃ p, e = prefixEdge P G s p) ∨ (∃ g, e = suffixEdge P G s g) ∨
      (∃ w, e = weakEdge P G s w) := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | exact .inl ⟨e,rfl⟩
    | (rcases e with ⟨b,e⟩; cases b
       · exact .inr (.inl ⟨e,rfl⟩)
       · exact .inr (.inr ⟨e,rfl⟩))

def iso : DeepIso (left P G s) (right P G s) where
  vertices := vertices P G s
  edges := edges P G s
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | rfl
      | (cases b; rfl; rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v)
  edge_label e := by
    rcases edge_cases P G s e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    all_goals cases d <;> exact labelEquiv_refl _ _
  source e := by
    rcases edge_cases P G s e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · cases d
      all_goals
        change ((P.source e).map (BoundarySerial.leftInsert P (adjoin G s))).map _ =
          (adjoin (Serial.net P G) s).source ⟨false,⟨false,e⟩⟩
        rw [adjoin_source]
        change ((P.source e).map _).map _ = ((P.source e).map _).map _
        rw [List.map_map,List.map_map]
        exact List.map_congr_left (fun v _ => prefix_commutes P G s v)
    · cases d
      all_goals
        change (((adjoin G s).source ⟨false,e⟩).map _).map _ =
          (adjoin (Serial.net P G) s).source ⟨false,⟨true,e⟩⟩
        rw [adjoin_source,adjoin_source]
        change (((G.source e).map _).map _).map _ = ((G.source e).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => suffix_commutes P G s v)
    · cases d <;> rfl
  target e := by
    rcases edge_cases P G s e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · cases d
      all_goals
        change ((P.target e).map (BoundarySerial.leftInsert P (adjoin G s))).map _ =
          (adjoin (Serial.net P G) s).target ⟨false,⟨false,e⟩⟩
        rw [adjoin_target]
        change ((P.target e).map _).map _ = ((P.target e).map _).map _
        rw [List.map_map,List.map_map]
        exact List.map_congr_left (fun v _ => prefix_commutes P G s v)
    · cases d
      all_goals
        change (((adjoin G s).target ⟨false,e⟩).map _).map _ =
          (adjoin (Serial.net P G) s).target ⟨false,⟨true,e⟩⟩
        rw [adjoin_target,adjoin_target]
        change (((G.target e).map _).map _).map _ = ((G.target e).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => suffix_commutes P G s v)
    · cases d
      all_goals
        change (((adjoin G s).target ⟨true,e⟩).map _).map _ =
          (adjoin (Serial.net P G) s).target ⟨true,e⟩
        rw [adjoin_weakening_target,adjoin_weakening_target]
        simp only [List.map_cons,List.map_nil]
        apply congrArg List.singleton
        change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 I J (A ++ s.wire :: B)).targetPort true
          (weakeningOutput A B s))) = _
        simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
        rfl

end Hypernets.Copying.BoxPullWeakening.SerialPull
