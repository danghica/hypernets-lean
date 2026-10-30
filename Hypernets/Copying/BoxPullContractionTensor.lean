import Hypernets.Copying.BoxPullContractionCoordinates

/-! Pull a contraction out of the first parallel operand without changing
the order of the other operand's ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.TensorPull
open Graph
variable {d : Nat} {I J A B O : List Wire}
  (s : ShareSort) (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) (V : Hypernet d J O)

abbrev left := Net.Tensor.net (merge s G) V
def right : Hypernet d (I ++ J) ((A ++ s.wire :: B) ++ O) :=
  (merge (A := A) (B := B ++ O) s ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).reboundary
    rfl (by simp only [List.append_assoc,List.cons_append])

def vertices : Bijection (left s G V).Internal (right s G V).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,.inl j⟩ => .inl j
      | ⟨false,.inr ⟨false,v⟩⟩ => .inr ⟨false,⟨false,v⟩⟩
      | ⟨false,.inr ⟨true,v⟩⟩ => nomatch v
      | ⟨true,v⟩ => .inr ⟨false,⟨true,v⟩⟩
    invFun := fun
      | .inl j => ⟨false,.inl j⟩
      | .inr ⟨false,⟨false,v⟩⟩ => ⟨false,.inr ⟨false,v⟩⟩
      | .inr ⟨false,⟨true,v⟩⟩ => ⟨true,v⟩
      | .inr ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro ⟨b,v⟩; cases b
      · rcases v with j | ⟨b,v⟩; rfl; cases b; rfl; exact nomatch v
      · rfl
    right_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rcases v with ⟨b,v⟩; cases b <;> rfl
        · exact nomatch v }

def edges : Bijection (left s G V).Edge (right s G V).Edge := by
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

abbrev firstPort (v : G.Vertex) : (left s G V).Vertex :=
  Net.Parallel.embed (Net.Tensor.family (merge s G) V) (Net.Tensor.boundary _ _ _ _) false
    (oldPort s G v)
abbrev secondPort (v : V.Vertex) : (left s G V).Vertex :=
  Net.Parallel.embed (Net.Tensor.family (merge s G) V) (Net.Tensor.boundary _ _ _ _) true v
abbrev rightFirstPort (v : G.Vertex) : (right s G V).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort (A := A) (B := B ++ O) s ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))
      (Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
        (Net.Parallel.embed (Net.Tensor.family G V) (Net.Tensor.boundary _ _ _ _) false v)))
abbrev rightSecondPort (v : V.Vertex) : (right s G V).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort (A := A) (B := B ++ O) s ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))
      (Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
        (Net.Parallel.embed (Net.Tensor.family G V) (Net.Tensor.boundary _ _ _ _) true v)))

theorem first_commutes (v : G.Vertex) :
    Port.map (vertices s G V).toFun (firstPort s G V v) = rightFirstPort s G V v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => rfl
  | output i =>
    cases d
    all_goals
      by_cases before : i.val < A.length
      · simp [firstPort,rightFirstPort,Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,oldPort,Port.cast,before] <;> rfl
      · by_cases middle : i.val < A.length+2
        · simp [firstPort,rightFirstPort,Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,oldPort,Port.cast,before,middle] <;> rfl
        · simp [firstPort,rightFirstPort,Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,oldPort,Port.cast,before,middle] <;> rfl

theorem second_commutes (v : V.Vertex) :
    Port.map (vertices s G V).toFun (secondPort s G V v) = rightSecondPort s G V v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => rfl
  | output i =>
    have before : ¬ A.length+(B.length+1+1)+i.val < A.length := by omega
    have middle : ¬ A.length+(B.length+1+1)+i.val < A.length+2 := by omega
    cases d
    all_goals
      simp [secondPort,rightSecondPort,Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,oldPort,Port.cast,before,middle]
      apply congrArg Port.output
      apply Fin.ext
      dsimp
      omega

def leftFirstEdge (e : G.Edge) : (left s G V).Edge := by cases d <;> exact ⟨false,⟨false,e⟩⟩
def rightFirstEdge (e : G.Edge) : (right s G V).Edge := by cases d <;> exact ⟨false,⟨false,e⟩⟩
def leftSecondEdge (e : V.Edge) : (left s G V).Edge := by cases d <;> exact ⟨true,e⟩
def rightSecondEdge (e : V.Edge) : (right s G V).Edge := by cases d <;> exact ⟨false,⟨true,e⟩⟩
def leftContraction (e : (primitiveNet d (.contraction s)).Edge) : (left s G V).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def rightContraction (e : (primitiveNet d (.contraction s)).Edge) : (right s G V).Edge := by
  cases d <;> exact ⟨true,e⟩

theorem first_source (e : G.Edge) :
    (left s G V).source (leftFirstEdge s G V e) = (G.source e).map (firstPort s G V) := by
  cases d
  all_goals
    change ((merge s G).source ⟨false,e⟩).map _ = _
    refine (congrArg (List.map (Net.Parallel.embed (Net.Tensor.family (merge s G) V)
      (Net.Tensor.boundary _ _ _ _) false)) (merge_source s G e)).trans ?_
    rw [List.map_map]
    rfl

theorem first_target (e : G.Edge) :
    (left s G V).target (leftFirstEdge s G V e) = (G.target e).map (firstPort s G V) := by
  cases d
  all_goals
    change ((merge s G).target ⟨false,e⟩).map _ = _
    refine (congrArg (List.map (Net.Parallel.embed (Net.Tensor.family (merge s G) V)
      (Net.Tensor.boundary _ _ _ _) false)) (merge_target s G e)).trans ?_
    rw [List.map_map]
    rfl

theorem right_first_source (e : G.Edge) :
    (right s G V).source (rightFirstEdge s G V e) = (G.source e).map (rightFirstPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s
      ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).source
      ⟨false,⟨false,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_source s ((Net.Tensor.net G V).reboundary rfl
      (by simp only [List.append_assoc,List.cons_append])) ⟨false,e⟩)).trans ?_
    change ((((G.source e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    rfl

theorem right_first_target (e : G.Edge) :
    (right s G V).target (rightFirstEdge s G V e) = (G.target e).map (rightFirstPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s
      ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).target
      ⟨false,⟨false,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_target s ((Net.Tensor.net G V).reboundary rfl
      (by simp only [List.append_assoc,List.cons_append])) ⟨false,e⟩)).trans ?_
    change ((((G.target e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    rfl

theorem right_second_source (e : V.Edge) :
    (right s G V).source (rightSecondEdge s G V e) = (V.source e).map (rightSecondPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s
      ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).source
      ⟨false,⟨true,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_source s ((Net.Tensor.net G V).reboundary rfl
      (by simp only [List.append_assoc,List.cons_append])) ⟨true,e⟩)).trans ?_
    change ((((V.source e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    rfl

theorem right_second_target (e : V.Edge) :
    (right s G V).target (rightSecondEdge s G V e) = (V.target e).map (rightSecondPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s
      ((Net.Tensor.net G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).target
      ⟨false,⟨true,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_target s ((Net.Tensor.net G V).reboundary rfl
      (by simp only [List.append_assoc,List.cons_append])) ⟨true,e⟩)).trans ?_
    change ((((V.target e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    rfl

theorem edge_cases (e : (left s G V).Edge) :
    (∃ a, e = leftFirstEdge s G V a) ∨ (∃ a, e = leftSecondEdge s G V a) ∨
      (∃ a, e = leftContraction s G V a) := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | exact .inr (.inl ⟨e,rfl⟩)
    | (rcases e with ⟨b,e⟩; cases b
       · exact .inl ⟨e,rfl⟩
       · exact .inr (.inr ⟨e,rfl⟩))

def iso : DeepIso (left s G V) (right s G V) where
  vertices := vertices s G V
  edges := edges s G V
  internal_label v := by
    cases d <;> rcases v with ⟨b,v⟩ <;> cases b
    all_goals first | rfl | (rcases v with j | ⟨b,v⟩; rfl; cases b; rfl; exact nomatch v)
  edge_label e := by
    rcases edge_cases s G V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    all_goals cases d <;> exact labelEquiv_refl _ _
  source e := by
    rcases edge_cases s G V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · cases d
      all_goals
        change ((left s G V).source (leftFirstEdge s G V e)).map _ =
        (right s G V).source (rightFirstEdge s G V e)
        rw [first_source,right_first_source,List.map_map]
        exact List.map_congr_left (fun v _ => first_commutes s G V v)
    · cases d
      all_goals
        change ((V.source e).map (secondPort s G V)).map _ =
        (right s G V).source (rightSecondEdge s G V e)
        rw [right_second_source,List.map_map]
        exact List.map_congr_left (fun v _ => second_commutes s G V v)
    · cases d
      all_goals
        change Fin 1 at e
        have he : e = 0 := Fin.ext (by omega)
        subst e
        rfl
  target e := by
    rcases edge_cases s G V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · cases d
      all_goals
        change ((left s G V).target (leftFirstEdge s G V e)).map _ =
        (right s G V).target (rightFirstEdge s G V e)
        rw [first_target,right_first_target,List.map_map]
        exact List.map_congr_left (fun v _ => first_commutes s G V v)
    · cases d
      all_goals
        change ((V.target e).map (secondPort s G V)).map _ =
        (right s G V).target (rightSecondEdge s G V e)
        rw [right_second_target,List.map_map]
        exact List.map_congr_left (fun v _ => second_commutes s G V v)
    · cases d
      all_goals
        change Fin 1 at e
        have he : e = 0 := Fin.ext (by omega)
        subst e
        rfl

end Hypernets.Copying.BoxPullContraction.TensorPull
