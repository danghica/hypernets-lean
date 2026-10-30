import Hypernets.Copying.BoxPullContractionCoordinates

/-! The geometric beta commutation underlying BPullC: attaching a contraction
to a body's free boundary commutes with connecting its bound output to the
unchanged argument. No evaluation or termination premise is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.Splice
open Graph Application
variable {d : Nat} {A B O : List Wire}
  (s : ShareSort) (G : Hypernet d [.term] (.term :: (A ++ s.wire :: s.wire :: B)))
  (V : Hypernet d [.term] O)

def left : Hypernet d [.term] ((A ++ s.wire :: B) ++ O) :=
  splice (merge (A := .term :: A) (B := B) s G) V

def right : Hypernet d [.term] ((A ++ s.wire :: B) ++ O) :=
  (merge (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).reboundary
    rfl (by simp only [List.append_assoc,List.cons_append])

/-- Reassociate the original body, the stable argument, the bound-output
junction and the two distinct contraction junctions. -/
def vertices : Bijection (left s G V).Internal (right s G V).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => .inr ⟨false,.inl j⟩
      | .inr ⟨false,.inl j⟩ => .inl j
      | .inr ⟨false,.inr ⟨false,v⟩⟩ => .inr ⟨false,.inr ⟨false,v⟩⟩
      | .inr ⟨false,.inr ⟨true,v⟩⟩ => nomatch v
      | .inr ⟨true,v⟩ => .inr ⟨false,.inr ⟨true,v⟩⟩
    invFun := fun
      | .inl j => .inr ⟨false,.inl j⟩
      | .inr ⟨false,.inl j⟩ => .inl j
      | .inr ⟨false,.inr ⟨false,v⟩⟩ => .inr ⟨false,.inr ⟨false,v⟩⟩
      | .inr ⟨false,.inr ⟨true,v⟩⟩ => .inr ⟨true,v⟩
      | .inr ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rcases v with j | ⟨b,v⟩; rfl; cases b; rfl; exact nomatch v
        · rfl
    right_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl
        · exact nomatch v }

/-- Every original edge is retained once. Only the position of the separate
contraction in the disjoint edge-carrier sum changes. -/
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

def leftBodyPort (v : G.Vertex) : (left s G V).Vertex :=
  SpliceBoundary.bodyInsert (merge (A := .term :: A) (B := B) s G) V
    (oldPort (A := .term :: A) (B := B) s G v)

def rightBodyPort (v : G.Vertex) : (right s G V).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))
      (Port.cast rfl (by simp only [List.append_assoc,List.cons_append]) (SpliceBoundary.bodyInsert G V v)))

def leftArgumentPort (v : V.Vertex) : (left s G V).Vertex :=
  SpliceBoundary.argumentInsert (merge (A := .term :: A) (B := B) s G) V v

def rightArgumentPort (v : V.Vertex) : (right s G V).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))
      (Port.cast rfl (by simp only [List.append_assoc,List.cons_append]) (SpliceBoundary.argumentInsert G V v)))

private theorem body_output {d F O} (B : Hypernet d [.term] (.term :: F))
    (V : Hypernet d [.term] O) (i : Fin (.term :: F).length) (positive : i.val ≠ 0) :
    SpliceBoundary.bodyInsert B V (.output i) =
      .output ⟨i.val-1,by have bound := i.isLt; simp at bound ⊢; omega⟩ := by
  have shape : ∃ j : Fin F.length, i = j.succ := by
    refine ⟨⟨i.val-1,by have bound : i.val < F.length+1 := i.isLt; omega⟩,?_⟩
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  obtain ⟨j,rfl⟩ := shape
  cases d <;> rfl

private theorem argument_output {d F O} (B : Hypernet d [.term] (.term :: F))
    (V : Hypernet d [.term] O) (i : Fin O.length) :
    SpliceBoundary.argumentInsert B V (.output i) =
      .output ⟨F.length+i.val,by simp⟩ := by cases d <;> rfl

/-- The actual embedding of each old body port commutes with reassociation,
including the bound output which becomes the internal argument junction. -/
theorem bodyPort_commutes (v : G.Vertex) :
    Port.map (vertices s G V).toFun (leftBodyPort s G V v) = rightBodyPort s G V v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => cases d <;> rfl
  | output i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases d <;> simp [leftBodyPort,rightBodyPort,oldPort,Port.cast] <;> rfl
    · cases d
      all_goals
        by_cases before : j.val < A.length
        · simp [body_output,leftBodyPort,rightBodyPort,oldPort,Port.cast,before,
            show j.val+1 < A.length+1 by omega] <;> rfl
        · by_cases middle : j.val < A.length+2
          · simp [body_output,leftBodyPort,rightBodyPort,oldPort,Port.cast,before,middle,
              show ¬j.val+1 < A.length+1 by omega,show j.val+1 < A.length+1+2 by omega,
              junction,vertices] <;> try rfl
          · simp [body_output,leftBodyPort,rightBodyPort,oldPort,Port.cast,before,middle,
              show ¬j.val+1 < A.length+1 by omega,show ¬j.val+1 < A.length+1+2 by omega,show j.val ≠ 0 by omega] <;> try rfl

/-- Every argument edge and port remains unchanged, including its arbitrary
atom and thunk outputs. -/
theorem argumentPort_commutes (v : V.Vertex) :
    Port.map (vertices s G V).toFun (leftArgumentPort s G V v) = rightArgumentPort s G V v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => cases d <;> rfl
  | output i =>
    cases d
    all_goals
      simp [argument_output,leftArgumentPort,rightArgumentPort,oldPort,Port.cast,
        show ¬A.length+(B.length+1+1)+i.val < A.length by omega,
        show ¬A.length+(B.length+1+1)+i.val < A.length+2 by omega]
      apply congrArg Port.output
      apply Fin.ext
      dsimp
      omega

def leftBodyEdge (e : G.Edge) : (left s G V).Edge := by
  cases d <;> exact ⟨false,⟨false,e⟩⟩
def rightBodyEdge (e : G.Edge) : (right s G V).Edge := by
  cases d <;> exact ⟨false,⟨false,e⟩⟩
def leftArgumentEdge (e : V.Edge) : (left s G V).Edge := by
  cases d <;> exact ⟨true,e⟩
def rightArgumentEdge (e : V.Edge) : (right s G V).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def leftContractionEdge (e : (primitiveNet d (.contraction s)).Edge) : (left s G V).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def rightContractionEdge (e : (primitiveNet d (.contraction s)).Edge) : (right s G V).Edge := by
  cases d <;> exact ⟨true,e⟩

theorem left_body_source (e : G.Edge) :
    (left s G V).source (leftBodyEdge s G V e) = (G.source e).map (leftBodyPort s G V) := by
  cases d
  all_goals
    change ((merge (A := .term :: A) s G).source ⟨false,e⟩).map _ = _
    refine (congrArg (List.map _) (merge_source (A := .term :: A) (B := B) s G e)).trans ?_
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => SpliceBoundary.body_insert _ V _)

theorem left_body_target (e : G.Edge) :
    (left s G V).target (leftBodyEdge s G V e) = (G.target e).map (leftBodyPort s G V) := by
  cases d
  all_goals
    change ((merge (A := .term :: A) s G).target ⟨false,e⟩).map _ = _
    refine (congrArg (List.map _) (merge_target (A := .term :: A) (B := B) s G e)).trans ?_
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => SpliceBoundary.body_insert _ V _)

theorem right_body_source (e : G.Edge) :
    (right s G V).source (rightBodyEdge s G V e) = (G.source e).map (rightBodyPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).source
      ⟨false,⟨false,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_source (A := A) (B := B ++ O) s _ _)).trans ?_
    change ((((G.source e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append])) (Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
      (SpliceBoundary.rawBodyInsert G V v))) = _
    rw [SpliceBoundary.body_insert]
    rfl

theorem right_body_target (e : G.Edge) :
    (right s G V).target (rightBodyEdge s G V e) = (G.target e).map (rightBodyPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).target
      ⟨false,⟨false,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_target (A := A) (B := B ++ O) s _ _)).trans ?_
    change ((((G.target e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append])) (Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
      (SpliceBoundary.rawBodyInsert G V v))) = _
    rw [SpliceBoundary.body_insert]
    rfl

theorem left_argument_source (e : V.Edge) :
    (left s G V).source (leftArgumentEdge s G V e) = (V.source e).map (leftArgumentPort s G V) := by
  cases d
  all_goals
    apply List.map_congr_left
    intro v _
    exact SpliceBoundary.argument_insert _ V v

theorem left_argument_target (e : V.Edge) :
    (left s G V).target (leftArgumentEdge s G V e) = (V.target e).map (leftArgumentPort s G V) := by
  cases d
  all_goals
    apply List.map_congr_left
    intro v _
    exact SpliceBoundary.argument_insert _ V v

theorem right_argument_source (e : V.Edge) :
    (right s G V).source (rightArgumentEdge s G V e) = (V.source e).map (rightArgumentPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).source
      ⟨false,⟨true,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_source (A := A) (B := B ++ O) s _ _)).trans ?_
    change ((((V.source e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append])) (Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
      (SpliceBoundary.rawArgumentInsert G V v))) = _
    rw [SpliceBoundary.argument_insert]
    rfl

theorem right_argument_target (e : V.Edge) :
    (right s G V).target (rightArgumentEdge s G V e) = (V.target e).map (rightArgumentPort s G V) := by
  cases d
  all_goals
    change ((merge (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append]))).target
      ⟨false,⟨true,e⟩⟩).map _ = _
    refine (congrArg (List.map _) (merge_target (A := A) (B := B ++ O) s _ _)).trans ?_
    change ((((V.target e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort (A := A) (B := B ++ O) s ((splice G V).reboundary rfl (by simp only [List.append_assoc,List.cons_append])) (Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
      (SpliceBoundary.rawArgumentInsert G V v))) = _
    rw [SpliceBoundary.argument_insert]
    rfl

theorem contraction_target (e : (primitiveNet d (.contraction s)).Edge) :
    ((left s G V).target (leftContractionEdge s G V e)).map (Port.map (vertices s G V).toFun) =
      (right s G V).target (rightContractionEdge s G V e) := by
  cases d
  all_goals
    change Fin 1 at e
    have eq : e = (0 : Fin 1) := Fin.ext (by omega)
    subst e
    change [Port.map (vertices s G V).toFun
      (SpliceBoundary.rawBodyInsert (merge (A := .term :: A) s G) V
        (.output ⟨A.length+1,by simp⟩))] = [Port.output ⟨A.length,by simp⟩]
    rw [SpliceBoundary.body_insert,body_output _ _ _ (by simp)]
    rfl

theorem edge_cases (e : (left s G V).Edge) :
    (∃ g, e = leftBodyEdge s G V g) ∨ (∃ v, e = leftArgumentEdge s G V v) ∨
      (∃ w, e = leftContractionEdge s G V w) := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | (rcases e with ⟨b,e⟩; cases b
       · exact .inl ⟨e,rfl⟩
       · exact .inr (.inr ⟨e,rfl⟩))
    | exact .inr (.inl ⟨e,rfl⟩)

theorem edges_body (e : G.Edge) :
    (edges s G V).toFun (leftBodyEdge s G V e) = rightBodyEdge s G V e := by cases d <;> rfl

theorem edges_argument (e : V.Edge) :
    (edges s G V).toFun (leftArgumentEdge s G V e) = rightArgumentEdge s G V e := by cases d <;> rfl

theorem edges_contraction (e : (primitiveNet d (.contraction s)).Edge) :
    (edges s G V).toFun (leftContractionEdge s G V e) = rightContractionEdge s G V e := by cases d <;> rfl

/-- Opening the bound output commutes with pulling out the contraction, up to
an ordered recursive graph isomorphism. This is independent of the argument's
behaviour and retains every edge of both original components. -/
def iso : DeepIso (left s G V) (right s G V) where
  vertices := vertices s G V
  edges := edges s G V
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | rfl
      | (cases b
         · rcases v with j | ⟨b,v⟩; rfl; cases b; rfl; exact nomatch v
         · rfl)
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | exact labelEquiv_refl _ _
      | (rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _)
  source e := by
    rcases edge_cases s G V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · change ((left s G V).source (leftBodyEdge s G V e)).map _ =
        (right s G V).source ((edges s G V).toFun (leftBodyEdge s G V e))
      rw [edges_body,left_body_source,right_body_source,List.map_map]
      exact List.map_congr_left (fun v _ => bodyPort_commutes s G V v)
    · change ((left s G V).source (leftArgumentEdge s G V e)).map _ =
        (right s G V).source ((edges s G V).toFun (leftArgumentEdge s G V e))
      rw [edges_argument,left_argument_source,right_argument_source,List.map_map]
      exact List.map_congr_left (fun v _ => argumentPort_commutes s G V v)
    · cases d <;> rfl
  target e := by
    rcases edge_cases s G V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · change ((left s G V).target (leftBodyEdge s G V e)).map _ =
        (right s G V).target ((edges s G V).toFun (leftBodyEdge s G V e))
      rw [edges_body,left_body_target,right_body_target,List.map_map]
      exact List.map_congr_left (fun v _ => bodyPort_commutes s G V v)
    · change ((left s G V).target (leftArgumentEdge s G V e)).map _ =
        (right s G V).target ((edges s G V).toFun (leftArgumentEdge s G V e))
      rw [edges_argument,left_argument_target,right_argument_target,List.map_map]
      exact List.map_congr_left (fun v _ => argumentPort_commutes s G V v)
    · change ((left s G V).target (leftContractionEdge s G V e)).map _ =
        (right s G V).target ((edges s G V).toFun (leftContractionEdge s G V e))
      rw [edges_contraction]
      exact contraction_target s G V e

end Hypernets.Copying.BoxPullContraction.Splice
