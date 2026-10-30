import Hypernets.Copying.BoxPullWeakeningSplice
import Hypernets.Copying.BoundarySerial

/-! Exact beta geometry for an ignored bound argument. The argument is
retained, with every original output, attached to the actual weakening. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundWeakeningSplice
open Graph Application BoxPullWeakening
variable {d : Nat} {F O : List Wire}
  (R : Hypernet d [.term] F) (V : Hypernet d [.term] O)

/-- The complete unused argument, including its original resource outputs. -/
def discarded : Hypernet d [] O := Serial.net (primitiveNet d (.weakening .term)) V

def left : Hypernet d [.term] (F ++ O) :=
  splice (adjoin (A := []) (B := F) R .term) V

def right : Hypernet d [.term] (F ++ O) :=
  (Net.Tensor.net R (discarded V)).reboundary (List.append_nil [Wire.term]) rfl

def vertices : Bijection (left R V).Internal (right R V).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => ⟨true,.inl j⟩
      | .inr ⟨false,⟨false,v⟩⟩ => ⟨false,v⟩
      | .inr ⟨false,⟨true,v⟩⟩ => nomatch v
      | .inr ⟨true,v⟩ => ⟨true,.inr ⟨true,v⟩⟩
    invFun := fun
      | ⟨false,v⟩ => .inr ⟨false,⟨false,v⟩⟩
      | ⟨true,.inl j⟩ => .inl j
      | ⟨true,.inr ⟨false,v⟩⟩ => nomatch v
      | ⟨true,.inr ⟨true,v⟩⟩ => .inr ⟨true,v⟩
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · rfl
      · cases b
        · rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v
        · rfl
    right_inv := by
      rintro ⟨b,v⟩
      cases b
      · rfl
      · rcases v with j | ⟨b,v⟩; rfl; cases b; exact nomatch v; rfl }

def edges : Bijection (left R V).Edge (right R V).Edge := by
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

def leftBodyPort (v : R.Vertex) : (left R V).Vertex :=
  SpliceBoundary.bodyInsert (adjoin (A := []) R .term) V (oldPort (A := []) R .term v)

def rightBodyPort (v : R.Vertex) : (right R V).Vertex :=
  Port.cast (List.append_nil [Wire.term]) rfl
    (Net.Parallel.embed (Net.Tensor.family R (discarded V)) (Net.Tensor.boundary _ _ _ _) false v)

def leftArgumentPort (v : V.Vertex) : (left R V).Vertex :=
  SpliceBoundary.argumentInsert (adjoin (A := []) R .term) V v

def rightArgumentPort (v : V.Vertex) : (right R V).Vertex :=
  Port.cast (List.append_nil [Wire.term]) rfl
    (Net.Parallel.embed (Net.Tensor.family R (discarded V)) (Net.Tensor.boundary _ _ _ _) true
      (BoundarySerial.rightInsert (primitiveNet d (.weakening .term)) V v))

theorem bodyPort_commutes (v : R.Vertex) :
    Port.map (vertices R V).toFun (leftBodyPort R V v) = rightBodyPort R V v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => cases d <;> rfl
  | output i =>
    have idx : oldOutput [] F .term i = i.succ := Fin.ext rfl
    cases d
    all_goals
      simp only [leftBodyPort,oldPort,idx]
      rfl

private theorem discarded_input (i : Fin [Wire.term].length) :
    BoundarySerial.rightInsert (primitiveNet d (.weakening .term)) V (.input i) =
      (.internal (.inl i) : (discarded V).Vertex) := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 [] [.term] O).sourcePort true i) = _
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

private theorem discarded_output (i : Fin O.length) :
    BoundarySerial.rightInsert (primitiveNet d (.weakening .term)) V (.output i) =
      (.output i : (discarded V).Vertex) := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 [] [.term] O).targetPort true i) = _
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

theorem argumentPort_commutes (v : V.Vertex) :
    Port.map (vertices R V).toFun (leftArgumentPort R V v) = rightArgumentPort R V v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i =>
    dsimp only [rightArgumentPort]
    rw [discarded_input]
    cases d <;> rfl
  | output i =>
    dsimp only [rightArgumentPort]
    rw [discarded_output]
    cases d <;> rfl

def leftBodyEdge (e : R.Edge) : (left R V).Edge := by cases d <;> exact ⟨false,⟨false,e⟩⟩
def rightBodyEdge (e : R.Edge) : (right R V).Edge := by cases d <;> exact ⟨false,e⟩
def leftArgumentEdge (e : V.Edge) : (left R V).Edge := by cases d <;> exact ⟨true,e⟩
def rightArgumentEdge (e : V.Edge) : (right R V).Edge := by cases d <;> exact ⟨true,⟨true,e⟩⟩
def leftWeakeningEdge (e : (primitiveNet d (.weakening .term)).Edge) : (left R V).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def rightWeakeningEdge (e : (primitiveNet d (.weakening .term)).Edge) : (right R V).Edge := by
  cases d <;> exact ⟨true,⟨false,e⟩⟩

theorem left_body_source (e : R.Edge) :
    (left R V).source (leftBodyEdge R V e) = (R.source e).map (leftBodyPort R V) := by
  cases d
  all_goals
    change ((adjoin (A := []) R .term).source ⟨false,e⟩).map _ = _
    rw [adjoin_source,List.map_map]
    exact List.map_congr_left (fun v _ => SpliceBoundary.body_insert _ V _)

theorem left_body_target (e : R.Edge) :
    (left R V).target (leftBodyEdge R V e) = (R.target e).map (leftBodyPort R V) := by
  cases d
  all_goals
    change ((adjoin (A := []) R .term).target ⟨false,e⟩).map _ = _
    rw [adjoin_target,List.map_map]
    exact List.map_congr_left (fun v _ => SpliceBoundary.body_insert _ V _)

theorem right_body_source (e : R.Edge) :
    (right R V).source (rightBodyEdge R V e) = (R.source e).map (rightBodyPort R V) := by
  cases d <;> exact List.map_map

theorem right_body_target (e : R.Edge) :
    (right R V).target (rightBodyEdge R V e) = (R.target e).map (rightBodyPort R V) := by
  cases d <;> exact List.map_map

theorem left_argument_source (e : V.Edge) :
    (left R V).source (leftArgumentEdge R V e) = (V.source e).map (leftArgumentPort R V) := by
  cases d <;> exact List.map_congr_left (fun v _ => SpliceBoundary.argument_insert _ V v)

theorem left_argument_target (e : V.Edge) :
    (left R V).target (leftArgumentEdge R V e) = (V.target e).map (leftArgumentPort R V) := by
  cases d <;> exact List.map_congr_left (fun v _ => SpliceBoundary.argument_insert _ V v)

theorem right_argument_source (e : V.Edge) :
    (right R V).source (rightArgumentEdge R V e) = (V.source e).map (rightArgumentPort R V) := by
  cases d <;> exact List.map_map.trans List.map_map

theorem right_argument_target (e : V.Edge) :
    (right R V).target (rightArgumentEdge R V e) = (V.target e).map (rightArgumentPort R V) := by
  cases d <;> exact List.map_map.trans List.map_map

theorem weakening_target (e : (primitiveNet d (.weakening .term)).Edge) :
    ((left R V).target (leftWeakeningEdge R V e)).map (Port.map (vertices R V).toFun) =
      (right R V).target (rightWeakeningEdge R V e) := by
  cases d
  all_goals
    change (((adjoin (A := []) R .term).target ⟨true,e⟩).map _).map _ = _
    rw [adjoin_weakening_target]
    simp only [List.map_cons,List.map_nil]
    change [Port.map _ (SpliceBoundary.rawBodyInsert _ V (.output 0))] = _
    rw [SpliceBoundary.body_insert]
    rfl

theorem edge_cases (e : (left R V).Edge) :
    (∃ g, e = leftBodyEdge R V g) ∨ (∃ v, e = leftArgumentEdge R V v) ∨
      (∃ w, e = leftWeakeningEdge R V w) := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | (rcases e with ⟨b,e⟩; cases b
       · exact .inl ⟨e,rfl⟩
       · exact .inr (.inr ⟨e,rfl⟩))
    | exact .inr (.inl ⟨e,rfl⟩)

theorem edges_body (e : R.Edge) :
    (edges R V).toFun (leftBodyEdge R V e) = rightBodyEdge R V e := by cases d <;> rfl
theorem edges_argument (e : V.Edge) :
    (edges R V).toFun (leftArgumentEdge R V e) = rightArgumentEdge R V e := by cases d <;> rfl
theorem edges_weakening (e : (primitiveNet d (.weakening .term)).Edge) :
    (edges R V).toFun (leftWeakeningEdge R V e) = rightWeakeningEdge R V e := by cases d <;> rfl

/-- Beta does not erase an ignored stable argument. It exposes precisely a
separate weakening connected to that entire argument, preserving all edges,
recursive box labels, output order and the active input. -/
def iso : DeepIso (left R V) (right R V) where
  vertices := vertices R V
  edges := edges R V
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | (have h : j = (0 : Fin 1) := Fin.ext (by have := j.isLt; change j.val < 1 at this; change j.val = 0; omega); subst j; rfl)
      | (cases b; rcases v with ⟨b,v⟩; cases b; rfl; exact nomatch v; rfl)
  edge_label e := by
    rcases edge_cases R V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    all_goals cases d <;> exact labelEquiv_refl _ _
  source e := by
    rcases edge_cases R V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · rw [edges_body]
      rw [left_body_source,right_body_source,List.map_map]
      exact List.map_congr_left (fun v _ => bodyPort_commutes R V v)
    · rw [edges_argument]
      rw [left_argument_source,right_argument_source,List.map_map]
      exact List.map_congr_left (fun v _ => argumentPort_commutes R V v)
    · cases d <;> rfl
  target e := by
    rcases edge_cases R V e with ⟨e,rfl⟩ | ⟨e,rfl⟩ | ⟨e,rfl⟩
    · rw [edges_body]
      rw [left_body_target,right_body_target,List.map_map]
      exact List.map_congr_left (fun v _ => bodyPort_commutes R V v)
    · rw [edges_argument]
      rw [left_argument_target,right_argument_target,List.map_map]
      exact List.map_congr_left (fun v _ => argumentPort_commutes R V v)
    · rw [edges_weakening]
      exact weakening_target R V e

end Hypernets.Copying.BoundWeakeningSplice
