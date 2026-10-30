import Hypernets.Copying.BoxPullWeakeningCoordinates

/-! Pull an unused resource out of the first parallel operand without changing
the order of the other operand's ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.TensorPull
open Graph
variable {d : Nat} {I J A B O : List Wire}
  (G : Hypernet d I (A ++ B)) (V : Hypernet d J O) (s : ShareSort)

abbrev left := Net.Tensor.net (adjoin G s) V
def right : Hypernet d (I ++ J) ((A ++ s.wire :: B) ++ O) :=
  (adjoin ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s).reboundary
    rfl (by simp only [List.append_assoc,List.cons_append])

def vertices : Bijection (left G V s).Internal (right G V s).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,⟨false,v⟩⟩ => ⟨false,⟨false,v⟩⟩
      | ⟨false,⟨true,v⟩⟩ => nomatch v
      | ⟨true,v⟩ => ⟨false,⟨true,v⟩⟩
    invFun := fun
      | ⟨false,⟨false,v⟩⟩ => ⟨false,⟨false,v⟩⟩
      | ⟨false,⟨true,v⟩⟩ => ⟨true,v⟩
      | ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro ⟨b,v⟩; cases b
      · rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v
      · rfl
    right_inv := by
      rintro ⟨b,v⟩; cases b
      · rcases v with ⟨b,v⟩; cases b <;> rfl
      · exact nomatch v }

def edges : Bijection (left G V s).Edge (right G V s).Edge := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,⟨false,e⟩⟩ => ⟨false,⟨false,e⟩⟩
      | ⟨false,⟨true,e⟩⟩ => ⟨true,e⟩
      | ⟨true,e⟩ => ⟨false,⟨true,e⟩⟩
    invFun := fun
      | ⟨false,⟨false,e⟩⟩ => ⟨false,⟨false,e⟩⟩
      | ⟨false,⟨true,e⟩⟩ => ⟨true,e⟩
      | ⟨true,e⟩ => ⟨false,⟨true,e⟩⟩
    left_inv := by rintro ⟨b,e⟩; cases b; rcases e with ⟨b,e⟩; cases b <;> rfl; rfl
    right_inv := by rintro ⟨b,e⟩; cases b; rcases e with ⟨b,e⟩; cases b <;> rfl; rfl }

abbrev firstPort (v : G.Vertex) : (left G V s).Vertex :=
  Net.Parallel.embed (Net.Tensor.family (adjoin G s) V) (Net.Tensor.boundary _ _ _ _) false
    (oldPort G s v)
abbrev secondPort (v : V.Vertex) : (left G V s).Vertex :=
  Net.Parallel.embed (Net.Tensor.family (adjoin G s) V) (Net.Tensor.boundary _ _ _ _) true v
abbrev rightFirstPort (v : G.Vertex) : (right G V s).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s
      (Port.cast rfl (List.append_assoc A B O)
        (Net.Parallel.embed (Net.Tensor.family G V) (Net.Tensor.boundary _ _ _ _) false v)))
abbrev rightSecondPort (v : V.Vertex) : (right G V s).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s
      (Port.cast rfl (List.append_assoc A B O)
        (Net.Parallel.embed (Net.Tensor.family G V) (Net.Tensor.boundary _ _ _ _) true v)))

theorem first_commutes (v : G.Vertex) :
    Port.map (vertices G V s).toFun (firstPort G V s v) = rightFirstPort G V s v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => rfl
  | output i =>
    apply congrArg Port.output
    apply Fin.ext
    rfl

theorem second_commutes (v : V.Vertex) :
    Port.map (vertices G V s).toFun (secondPort G V s v) = rightSecondPort G V s v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => rfl
  | output i =>
    apply congrArg Port.output
    apply Fin.ext
    change (A ++ s.wire :: B).length + i.val =
      if (A ++ B).length + i.val < A.length then (A ++ B).length + i.val
      else (A ++ B).length + i.val + 1
    simp only [List.length_append,List.length_cons]
    split <;> omega

theorem first_source (e : G.Edge) :
    (left G V s).source ⟨false,⟨false,e⟩⟩ = (G.source e).map (firstPort G V s) := by
  change ((adjoin G s).source ⟨false,e⟩).map _ = _
  rw [adjoin_source,List.map_map]
  rfl
theorem first_target (e : G.Edge) :
    (left G V s).target ⟨false,⟨false,e⟩⟩ = (G.target e).map (firstPort G V s) := by
  change ((adjoin G s).target ⟨false,e⟩).map _ = _
  rw [adjoin_target,List.map_map]
  rfl
theorem right_first_source (e : G.Edge) :
    (right G V s).source ⟨false,⟨false,e⟩⟩ = (G.source e).map (rightFirstPort G V s) := by
  change ((adjoin ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s).source
    ⟨false,⟨false,e⟩⟩).map _ = _
  rw [adjoin_source]
  change ((((G.source e).map _).map _).map _).map _ = _
  simp only [List.map_map]
  rfl
theorem right_first_target (e : G.Edge) :
    (right G V s).target ⟨false,⟨false,e⟩⟩ = (G.target e).map (rightFirstPort G V s) := by
  change ((adjoin ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s).target
    ⟨false,⟨false,e⟩⟩).map _ = _
  rw [adjoin_target]
  change ((((G.target e).map _).map _).map _).map _ = _
  simp only [List.map_map]
  rfl
theorem right_second_source (e : V.Edge) :
    (right G V s).source ⟨false,⟨true,e⟩⟩ = (V.source e).map (rightSecondPort G V s) := by
  change ((adjoin ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s).source
    ⟨false,⟨true,e⟩⟩).map _ = _
  rw [adjoin_source]
  change ((((V.source e).map _).map _).map _).map _ = _
  simp only [List.map_map]
  rfl
theorem right_second_target (e : V.Edge) :
    (right G V s).target ⟨false,⟨true,e⟩⟩ = (V.target e).map (rightSecondPort G V s) := by
  change ((adjoin ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s).target
    ⟨false,⟨true,e⟩⟩).map _ = _
  rw [adjoin_target]
  change ((((V.target e).map _).map _).map _).map _ = _
  simp only [List.map_map]
  rfl

def iso : DeepIso (left G V s) (right G V s) where
  vertices := vertices G V s
  edges := edges G V s
  internal_label v := by
    cases d <;> rcases v with ⟨b,v⟩ <;> cases b
    all_goals first | rfl | (rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v)
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first | exact labelEquiv_refl _ _ | (rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _)
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b
         · change ((left G V s).source ⟨false,⟨false,e⟩⟩).map _ = (right G V s).source ⟨false,⟨false,e⟩⟩
           rw [first_source,right_first_source,List.map_map]
           exact List.map_congr_left (fun v _ => first_commutes G V s v)
         · rfl)
      | (change ((V.source e).map (secondPort G V s)).map _ = (right G V s).source ⟨false,⟨true,e⟩⟩
         rw [right_second_source,List.map_map]
         exact List.map_congr_left (fun v _ => second_commutes G V s v))
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b
         · change ((left G V s).target ⟨false,⟨false,e⟩⟩).map _ = (right G V s).target ⟨false,⟨false,e⟩⟩
           rw [first_target,right_first_target,List.map_map]
           exact List.map_congr_left (fun v _ => first_commutes G V s v)
         · change (((adjoin G s).target ⟨true,e⟩).map _).map _ =
             ((adjoin ((Net.Tensor.net G V).reboundary rfl (List.append_assoc A B O)) s).target ⟨true,e⟩).map _
           rw [adjoin_weakening_target,adjoin_weakening_target]
           rfl)
      | (change ((V.target e).map (secondPort G V s)).map _ = (right G V s).target ⟨false,⟨true,e⟩⟩
         rw [right_second_target,List.map_map]
         exact List.map_congr_left (fun v _ => second_commutes G V s v))

end Hypernets.Copying.BoxPullWeakening.TensorPull
