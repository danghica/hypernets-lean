import Hypernets.Copying.NullaryParallelSerial
import Hypernets.Copying.CombinedLocality

/-! Move a closed-output branch past a serial connection on an independently
sourced neighbour. All graph edges and the ordered external boundary are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ClosedBranchSerial
open Graph
variable {d I K J O} (G : Hypernet d I []) (W : Hypernet d K J) (R : Hypernet d J O)

abbrev left := Serial.net (Net.Tensor.net G W) R
abbrev right := Net.Tensor.net G (Serial.net W R)

private def vertices : Bijection (left G W R).Internal (right G W R).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => ⟨true,.inl j⟩
      | .inr ⟨false,⟨false,v⟩⟩ => ⟨false,v⟩
      | .inr ⟨false,⟨true,v⟩⟩ => ⟨true,.inr ⟨false,v⟩⟩
      | .inr ⟨true,v⟩ => ⟨true,.inr ⟨true,v⟩⟩
    invFun := fun
      | ⟨false,v⟩ => .inr ⟨false,⟨false,v⟩⟩
      | ⟨true,.inl j⟩ => .inl j
      | ⟨true,.inr ⟨false,v⟩⟩ => .inr ⟨false,⟨true,v⟩⟩
      | ⟨true,.inr ⟨true,v⟩⟩ => .inr ⟨true,v⟩
    left_inv := by
      rintro (j | ⟨b,v⟩); rfl
      cases b
      · rcases v with ⟨b,v⟩; cases b <;> rfl
      · rfl
    right_inv := by
      rintro ⟨b,v⟩; cases b; rfl
      rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl }

private def edges : Bijection (left G W R).Edge (right G W R).Edge := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,⟨false,e⟩⟩ => ⟨false,e⟩
      | ⟨false,⟨true,e⟩⟩ => ⟨true,⟨false,e⟩⟩
      | ⟨true,e⟩ => ⟨true,⟨true,e⟩⟩
    invFun := fun
      | ⟨false,e⟩ => ⟨false,⟨false,e⟩⟩
      | ⟨true,⟨false,e⟩⟩ => ⟨false,⟨true,e⟩⟩
      | ⟨true,⟨true,e⟩⟩ => ⟨true,e⟩
    left_inv := by rintro ⟨b,e⟩; cases b; rcases e with ⟨b,e⟩; cases b <;> rfl; rfl
    right_inv := by rintro ⟨b,e⟩; cases b; rfl; rcases e with ⟨b,e⟩; cases b <;> rfl }

private theorem first_commutes (v : G.Vertex) :
    Port.map (vertices G W R).toFun
      (BoundarySerial.leftInsert _ R (Net.Parallel.embed (Net.Tensor.family G W) (Net.Tensor.boundary _ _ _ _) false v)) =
    Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary _ _ _ _) false v := by
  cases d <;> cases v with
  | internal v => rfl
  | output i => exact Fin.elim0 i
  | input i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 (I ++ K) J O).sourcePort false _)) = _
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]
    first | rfl | (simp only [Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,List.length_nil,Nat.zero_add] <;> rfl)

private theorem middle_commutes (v : W.Vertex) :
    Port.map (vertices G W R).toFun
      (BoundarySerial.leftInsert _ R (Net.Parallel.embed (Net.Tensor.family G W) (Net.Tensor.boundary _ _ _ _) true v)) =
    Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary _ _ _ _) true
      (BoundarySerial.leftInsert W R v) := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (BoundarySerial.leftInsert _ _ (.input _)) =
      Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary I [] K O) true (BoundarySerial.leftInsert W R (.input i))
    rw [Combined.left_input,Combined.left_input]
    rfl
  | output i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 (I ++ K) J O).targetPort false _)) =
      Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary I [] K O) true (Port.map Sum.inl ((Serial.pattern 0 K J O).targetPort false _))
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]
    first | rfl | (simp only [Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,List.length_nil,Nat.zero_add] <;> rfl)

private theorem last_commutes (v : R.Vertex) :
    Port.map (vertices G W R).toFun (BoundarySerial.rightInsert _ R v) =
    Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary _ _ _ _) true
      (BoundarySerial.rightInsert W R v) := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 (I ++ K) J O).sourcePort true _)) =
      Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary I [] K O) true (Port.map Sum.inl ((Serial.pattern 0 K J O).sourcePort true _))
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]
    first | rfl | (simp only [Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,List.length_nil,Nat.zero_add] <;> rfl)
  | output i =>
    change Port.map _ (Port.map Sum.inl ((Serial.pattern 0 (I ++ K) J O).targetPort true _)) =
      Net.Parallel.embed (Net.Tensor.family G (Serial.net W R)) (Net.Tensor.boundary I [] K O) true (Port.map Sum.inl ((Serial.pattern 0 K J O).targetPort true _))
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]
    first | rfl | (simp only [Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,List.length_nil,Nat.zero_add] <;> rfl)

/-- The independent graph may contain arbitrary nested boxes or state. Only
its empty output interface is needed to commute the neighbouring connection. -/
def iso : DeepIso (left G W R) (right G W R) where
  vertices := vertices G W R
  edges := edges G W R
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first | rfl | (cases b; rcases v with ⟨b,v⟩; cases b <;> rfl; rfl)
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first | exact labelEquiv_refl _ _ | (rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _)
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b
         · change ((((G.source e).map _).map _).map _) = (G.source e).map _
           simp only [List.map_map]
           exact List.map_congr_left (fun v _ => first_commutes G W R v)
         · change ((((W.source e).map _).map _).map _) = ((W.source e).map _).map _
           simp only [List.map_map]
           exact List.map_congr_left (fun v _ => middle_commutes G W R v))
      | (change (((R.source e).map _).map _) = ((R.source e).map _).map _
         simp only [List.map_map]
         exact List.map_congr_left (fun v _ => last_commutes G W R v))
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b
         · change ((((G.target e).map _).map _).map _) = (G.target e).map _
           simp only [List.map_map]
           exact List.map_congr_left (fun v _ => first_commutes G W R v)
         · change ((((W.target e).map _).map _).map _) = ((W.target e).map _).map _
           simp only [List.map_map]
           exact List.map_congr_left (fun v _ => middle_commutes G W R v))
      | (change (((R.target e).map _).map _) = ((R.target e).map _).map _
         simp only [List.map_map]
         exact List.map_congr_left (fun v _ => last_commutes G W R v))

end Hypernets.Copying.ClosedBranchSerial
