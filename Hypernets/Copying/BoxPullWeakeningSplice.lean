import Hypernets.Copying.BoxPullWeakeningCoordinates

/-! The geometric beta commutation underlying BPullW: adjoining a weakening
to a body's free boundary commutes with connecting its bound output to the
unchanged argument. No evaluation or termination premise is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.Splice
open Graph Application
variable {d : Nat} {A B O : List Wire}
  (G : Hypernet d [.term] (.term :: (A ++ B))) (V : Hypernet d [.term] O)
  (s : ShareSort)

def left : Hypernet d [.term] ((A ++ s.wire :: B) ++ O) :=
  splice (adjoin (A := .term :: A) (B := B) G s) V

def right : Hypernet d [.term] ((A ++ s.wire :: B) ++ O) :=
  (adjoin ((splice G V).reboundary rfl (List.append_assoc A B O)) s).reboundary
    rfl (by simp only [List.append_assoc,List.cons_append])

/-- Reassociate the original body and argument carriers and the same single
bound-output junction. The weakening has no internal vertices. -/
def vertices : Bijection (left G V s).Internal (right G V s).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => ⟨false,.inl j⟩
      | .inr ⟨false,⟨false,v⟩⟩ => ⟨false,.inr ⟨false,v⟩⟩
      | .inr ⟨false,⟨true,v⟩⟩ => nomatch v
      | .inr ⟨true,v⟩ => ⟨false,.inr ⟨true,v⟩⟩
    invFun := fun
      | ⟨false,.inl j⟩ => .inl j
      | ⟨false,.inr ⟨false,v⟩⟩ => .inr ⟨false,⟨false,v⟩⟩
      | ⟨false,.inr ⟨true,v⟩⟩ => .inr ⟨true,v⟩
      | ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v
        · rfl
    right_inv := by
      rintro ⟨b,v⟩
      cases b
      · rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl
      · exact nomatch v }

/-- Every original edge is retained once. Only the position of the separate
weakening in the disjoint edge-carrier sum changes. -/
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

def leftBodyPort (v : G.Vertex) : (left G V s).Vertex :=
  SpliceBoundary.bodyInsert (adjoin (A := .term :: A) (B := B) G s) V
    (oldPort (A := .term :: A) (B := B) G s v)

def rightBodyPort (v : G.Vertex) : (right G V s).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort ((splice G V).reboundary rfl (List.append_assoc A B O)) s
      (Port.cast rfl (List.append_assoc A B O) (SpliceBoundary.bodyInsert G V v)))

def leftArgumentPort (v : V.Vertex) : (left G V s).Vertex :=
  SpliceBoundary.argumentInsert (adjoin (A := .term :: A) (B := B) G s) V v

def rightArgumentPort (v : V.Vertex) : (right G V s).Vertex :=
  Port.cast rfl (by simp only [List.append_assoc,List.cons_append])
    (oldPort ((splice G V).reboundary rfl (List.append_assoc A B O)) s
      (Port.cast rfl (List.append_assoc A B O) (SpliceBoundary.argumentInsert G V v)))

theorem oldOutput_succ (i : Fin (A ++ B).length) :
    oldOutput (.term :: A) B s i.succ = (oldOutput A B s i).succ := by
  apply Fin.ext
  simp only [oldOutput,List.length_cons,Fin.val_succ,Nat.add_lt_add_iff_right]
  split <;> simp_all <;> omega

/-- The actual embedding of each old body port commutes with reassociation,
including the bound output which becomes the internal argument junction. -/
theorem bodyPort_commutes (v : G.Vertex) :
    Port.map (vertices G V s).toFun (leftBodyPort G V s v) = rightBodyPort G V s v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => cases d <;> rfl
  | output i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases d <;> rfl
    · cases d
      all_goals
        simp only [leftBodyPort,oldPort,oldOutput_succ]
        apply congrArg Port.output
        apply Fin.ext
        change (oldOutput A B s j).val = (oldOutput A (B ++ O) s
          ⟨j.val,by have := j.isLt; simp only [List.length_append] at *; omega⟩).val
        rfl

/-- The stable argument is untouched, including all its store and atom ports. -/
theorem argumentPort_commutes (v : V.Vertex) :
    Port.map (vertices G V s).toFun (leftArgumentPort G V s v) = rightArgumentPort G V s v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => cases d <;> rfl
  | output i =>
    cases d
    all_goals
      apply congrArg Port.output
      apply Fin.ext
      change (A ++ s.wire :: B).length + i.val =
        if (A ++ B).length + i.val < A.length then (A ++ B).length + i.val
        else (A ++ B).length + i.val + 1
      simp only [List.length_append,List.length_cons]
      split <;> omega

def leftBodyEdge (e : G.Edge) : (left G V s).Edge := by
  cases d <;> exact ⟨false,⟨false,e⟩⟩
def rightBodyEdge (e : G.Edge) : (right G V s).Edge := by
  cases d <;> exact ⟨false,⟨false,e⟩⟩
def leftArgumentEdge (e : V.Edge) : (left G V s).Edge := by
  cases d <;> exact ⟨true,e⟩
def rightArgumentEdge (e : V.Edge) : (right G V s).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def leftWeakeningEdge (e : (primitiveNet d (.weakening s)).Edge) : (left G V s).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def rightWeakeningEdge (e : (primitiveNet d (.weakening s)).Edge) : (right G V s).Edge := by
  cases d <;> exact ⟨true,e⟩

theorem left_body_source (e : G.Edge) :
    (left G V s).source (leftBodyEdge G V s e) = (G.source e).map (leftBodyPort G V s) := by
  cases d
  all_goals
    change ((adjoin (A := .term :: A) G s).source ⟨false,e⟩).map _ = _
    rw [adjoin_source,List.map_map]
    exact List.map_congr_left (fun v _ => SpliceBoundary.body_insert _ V _)

theorem left_body_target (e : G.Edge) :
    (left G V s).target (leftBodyEdge G V s e) = (G.target e).map (leftBodyPort G V s) := by
  cases d
  all_goals
    change ((adjoin (A := .term :: A) G s).target ⟨false,e⟩).map _ = _
    rw [adjoin_target,List.map_map]
    exact List.map_congr_left (fun v _ => SpliceBoundary.body_insert _ V _)

theorem right_body_source (e : G.Edge) :
    (right G V s).source (rightBodyEdge G V s e) = (G.source e).map (rightBodyPort G V s) := by
  cases d
  all_goals
    change ((adjoin ((splice G V).reboundary rfl (List.append_assoc A B O)) s).source
      ⟨false,⟨false,e⟩⟩).map _ = _
    rw [adjoin_source]
    change ((((G.source e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort ((splice G V).reboundary rfl (List.append_assoc A B O)) s (Port.cast rfl (List.append_assoc A B O)
      (SpliceBoundary.rawBodyInsert G V v))) = _
    rw [SpliceBoundary.body_insert]
    rfl

theorem right_body_target (e : G.Edge) :
    (right G V s).target (rightBodyEdge G V s e) = (G.target e).map (rightBodyPort G V s) := by
  cases d
  all_goals
    change ((adjoin ((splice G V).reboundary rfl (List.append_assoc A B O)) s).target
      ⟨false,⟨false,e⟩⟩).map _ = _
    rw [adjoin_target]
    change ((((G.target e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort ((splice G V).reboundary rfl (List.append_assoc A B O)) s (Port.cast rfl (List.append_assoc A B O)
      (SpliceBoundary.rawBodyInsert G V v))) = _
    rw [SpliceBoundary.body_insert]
    rfl

theorem left_argument_source (e : V.Edge) :
    (left G V s).source (leftArgumentEdge G V s e) = (V.source e).map (leftArgumentPort G V s) := by
  cases d
  all_goals
    apply List.map_congr_left
    intro v _
    exact SpliceBoundary.argument_insert _ V v

theorem left_argument_target (e : V.Edge) :
    (left G V s).target (leftArgumentEdge G V s e) = (V.target e).map (leftArgumentPort G V s) := by
  cases d
  all_goals
    apply List.map_congr_left
    intro v _
    exact SpliceBoundary.argument_insert _ V v

theorem right_argument_source (e : V.Edge) :
    (right G V s).source (rightArgumentEdge G V s e) = (V.source e).map (rightArgumentPort G V s) := by
  cases d
  all_goals
    change ((adjoin ((splice G V).reboundary rfl (List.append_assoc A B O)) s).source
      ⟨false,⟨true,e⟩⟩).map _ = _
    rw [adjoin_source]
    change ((((V.source e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort ((splice G V).reboundary rfl (List.append_assoc A B O)) s (Port.cast rfl (List.append_assoc A B O)
      (SpliceBoundary.rawArgumentInsert G V v))) = _
    rw [SpliceBoundary.argument_insert]
    rfl

theorem right_argument_target (e : V.Edge) :
    (right G V s).target (rightArgumentEdge G V s e) = (V.target e).map (rightArgumentPort G V s) := by
  cases d
  all_goals
    change ((adjoin ((splice G V).reboundary rfl (List.append_assoc A B O)) s).target
      ⟨false,⟨true,e⟩⟩).map _ = _
    rw [adjoin_target]
    change ((((V.target e).map _).map _).map _).map _ = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    dsimp only [Function.comp_apply]
    change Port.cast _ _ (oldPort ((splice G V).reboundary rfl (List.append_assoc A B O)) s (Port.cast rfl (List.append_assoc A B O)
      (SpliceBoundary.rawArgumentInsert G V v))) = _
    rw [SpliceBoundary.argument_insert]
    rfl

theorem weakening_target (e : (primitiveNet d (.weakening s)).Edge) :
    ((left G V s).target (leftWeakeningEdge G V s e)).map (Port.map (vertices G V s).toFun) =
      (right G V s).target (rightWeakeningEdge G V s e) := by
  cases d
  all_goals
    change (((adjoin (A := .term :: A) G s).target ⟨true,e⟩).map _).map _ =
      ((adjoin ((splice G V).reboundary rfl (List.append_assoc A B O)) s).target ⟨true,e⟩).map _
    rw [adjoin_weakening_target,adjoin_weakening_target]
    simp only [List.map_cons,List.map_nil]
    apply congrArg List.singleton
    change Port.map _ (SpliceBoundary.rawBodyInsert _ V (.output (weakeningOutput (.term :: A) B s))) = _
    rw [SpliceBoundary.body_insert]
    have idx : weakeningOutput (.term :: A) B s = (weakeningOutput A B s).succ := Fin.ext rfl
    rw [idx]
    rfl

theorem edge_cases (e : (left G V s).Edge) :
    (∃ g, e = leftBodyEdge G V s g) ∨ (∃ v, e = leftArgumentEdge G V s v) ∨
      (∃ w, e = leftWeakeningEdge G V s w) := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | (rcases e with ⟨b,e⟩; cases b
       · exact .inl ⟨e,rfl⟩
       · exact .inr (.inr ⟨e,rfl⟩))
    | exact .inr (.inl ⟨e,rfl⟩)

theorem edges_body (e : G.Edge) :
    (edges G V s).toFun (leftBodyEdge G V s e) = rightBodyEdge G V s e := by cases d <;> rfl

theorem edges_argument (e : V.Edge) :
    (edges G V s).toFun (leftArgumentEdge G V s e) = rightArgumentEdge G V s e := by cases d <;> rfl

theorem edges_weakening (e : (primitiveNet d (.weakening s)).Edge) :
    (edges G V s).toFun (leftWeakeningEdge G V s e) = rightWeakeningEdge G V s e := by cases d <;> rfl

/-- Opening the bound output commutes with pulling out the weakening, up to
an ordered recursive graph isomorphism. This is independent of the argument's
behaviour and retains every edge of both original components. -/
def iso : DeepIso (left G V s) (right G V s) where
  vertices := vertices G V s
  edges := edges G V s
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | rfl
      | (cases b; rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v; rfl)
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | exact labelEquiv_refl _ _
      | (rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _)
  source e := by
    rcases edge_cases G V s e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · change ((left G V s).source (leftBodyEdge G V s e)).map _ =
        (right G V s).source ((edges G V s).toFun (leftBodyEdge G V s e))
      rw [edges_body,left_body_source,right_body_source,List.map_map]
      exact List.map_congr_left (fun v _ => bodyPort_commutes G V s v)
    · change ((left G V s).source (leftArgumentEdge G V s e)).map _ =
        (right G V s).source ((edges G V s).toFun (leftArgumentEdge G V s e))
      rw [edges_argument,left_argument_source,right_argument_source,List.map_map]
      exact List.map_congr_left (fun v _ => argumentPort_commutes G V s v)
    · cases d <;> rfl
  target e := by
    rcases edge_cases G V s e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · change ((left G V s).target (leftBodyEdge G V s e)).map _ =
        (right G V s).target ((edges G V s).toFun (leftBodyEdge G V s e))
      rw [edges_body,left_body_target,right_body_target,List.map_map]
      exact List.map_congr_left (fun v _ => bodyPort_commutes G V s v)
    · change ((left G V s).target (leftArgumentEdge G V s e)).map _ =
        (right G V s).target ((edges G V s).toFun (leftArgumentEdge G V s e))
      rw [edges_argument,left_argument_target,right_argument_target,List.map_map]
      exact List.map_congr_left (fun v _ => argumentPort_commutes G V s v)
    · change ((left G V s).target (leftWeakeningEdge G V s e)).map _ =
        (right G V s).target ((edges G V s).toFun (leftWeakeningEdge G V s e))
      rw [edges_weakening]
      exact weakening_target G V s e

end Hypernets.Copying.BoxPullWeakening.Splice
