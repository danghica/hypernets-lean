import Hypernets.Copying.DiscardResult

/-! Source-determined replacement for both actual atom-equality branches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality
open Graph

/-- The comparison result is retained with two explicit argument weakenings. -/
def filler {d I O} (G : Hypernet d I O) (e : G.Edge)
    (label : G.edgeLabel e = primitiveLabel d (.operation (.binary .atomEq))) (b : Bool) :
    Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e)) :=
  (DiscardResult.net d (.bool b)).reboundary (by rw [label,primitive_input]; rfl)
    (by rw [label,primitive_output]; rfl)

/-- Canonical equality resumes at the old request wire and keeps every other edge. -/
noncomputable def canonical {d I O} (G : Hypernet d I O) (e : G.Edge)
    (label : G.edgeLabel e = primitiveLabel d (.operation (.binary .atomEq))) (v : G.Vertex) (b : Bool) :
    Combined.State d I O := Combined.Replacement.state G e (filler G e label b) v

/-- Renaming transports the entire canonical equality successor, including the token. -/
noncomputable def canonical_rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    (e : G.Edge) (label : G.edgeLabel e = primitiveLabel d (.operation (.binary .atomEq)))
    (v : G.Vertex) (b : Bool) :
    Combined.StateIso (canonical G e label v b)
      (canonical H (f.edges.toFun e) ((Search.primitive_equiv (f.edge_label e) _).mp label)
        (Port.map f.vertices.toFun v) b) := by
  have eq : (filler G e label b).reboundary (labelEquiv_input d (f.edge_label e))
      (labelEquiv_output d (f.edge_label e)) =
      filler H (f.edges.toFun e) ((Search.primitive_equiv (f.edge_label e) _).mp label) b := by
    unfold filler; rw [reboundary_comp]
  exact (Combined.Replacement.rename f e (filler G e label b) v).trans
    (Combined.StateIso.ofEq (congrArg (fun A => Combined.Replacement.state H (f.edges.toFun e) A
      (Port.map f.vertices.toFun v)) eq))

namespace Same

def head {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (before T d).Edge := ⟨.compare,(0 : Fin 1)⟩
theorem head_at {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    MatchEmbedding.HeadAt (before T d) (inputPort h 0) (head T d) (.operation (.binary .atomEq)) :=
  ⟨rfl,List.mem_cons_self⟩

/-- Source of the local isomorphism, retaining the atom tree and store as host edges. -/
noncomputable abbrev replaced {h} (T : ContractionTree .atom (h+2)) (d : Nat) :=
  (canonical (before T d) (head T d) (head_at T d).1 (inputPort h 0) true).1

/-- No internal wire is deleted: only the vacuous replacement component is eliminated. -/
def vertexTo {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (replaced T d).Internal → (after T d).Internal
  | .inl (.inl v) => .inl v
  | .inl (.inr ⟨.tree,v⟩) => .inr ⟨.tree,v⟩
  | .inl (.inr ⟨.compare,v⟩) => nomatch v
  | .inl (.inr ⟨.left,v⟩) => nomatch v
  | .inl (.inr ⟨.right,v⟩) => nomatch v
  | .inl (.inr ⟨.store,v⟩) => nomatch v
  | .inr v => nomatch v

def vertexFrom {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Internal → (replaced T d).Internal
  | .inl v => .inl (.inl v)
  | .inr ⟨.tree,v⟩ => .inl (.inr ⟨.tree,v⟩)
  | .inr ⟨.result,v⟩ => nomatch v
  | .inr ⟨.discardLeft,v⟩ => nomatch v
  | .inr ⟨.discardRight,v⟩ => nomatch v
  | .inr ⟨.left,v⟩ => nomatch v
  | .inr ⟨.right,v⟩ => nomatch v
  | .inr ⟨.store,v⟩ => nomatch v

def vertices {h} (T : ContractionTree .atom (h+2)) (d : Nat) : Bijection (replaced T d).Internal (after T d).Internal where
  toFun := vertexTo T d
  invFun := vertexFrom T d
  left_inv v := by
    rcases v with (v | ⟨e,v⟩) | v
    · rfl
    · cases e <;> first | rfl | exact nomatch v
    · exact nomatch v
  right_inv v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · cases e <;> first | rfl | exact nomatch v

/-- Every non-head edge retains its occurrence; the three fresh edges have fixed roles. -/
def edgeTo {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (replaced T d).Edge → (after T d).Edge
  | .inl ⟨⟨.compare,i⟩,ne⟩ => False.elim (ne (by have eq : i = (0 : Fin 1) := DiscardResult.fin_one i; cases eq; rfl))
  | .inl ⟨⟨.left,i⟩,_⟩ => ⟨.left,i⟩
  | .inl ⟨⟨.right,i⟩,_⟩ => ⟨.right,i⟩
  | .inl ⟨⟨.tree,i⟩,_⟩ => ⟨.tree,i⟩
  | .inl ⟨⟨.store,i⟩,_⟩ => ⟨.store,i⟩
  | .inr i => if i.val = 0 then ⟨.result,(0 : Fin 1)⟩ else
      if i.val = 1 then ⟨.discardLeft,(0 : Fin 1)⟩ else ⟨.discardRight,(0 : Fin 1)⟩

def edgeFrom {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge → (replaced T d).Edge
  | ⟨.result,_⟩ => .inr (0 : Fin 3)
  | ⟨.discardLeft,_⟩ => .inr (1 : Fin 3)
  | ⟨.discardRight,_⟩ => .inr (2 : Fin 3)
  | ⟨.left,i⟩ => .inl ⟨⟨.left,i⟩,by intro eq; cases eq⟩
  | ⟨.right,i⟩ => .inl ⟨⟨.right,i⟩,by intro eq; cases eq⟩
  | ⟨.tree,i⟩ => .inl ⟨⟨.tree,i⟩,by intro eq; cases eq⟩
  | ⟨.store,i⟩ => .inl ⟨⟨.store,i⟩,by intro eq; cases eq⟩

def edges {h} (T : ContractionTree .atom (h+2)) (d : Nat) : Bijection (replaced T d).Edge (after T d).Edge where
  toFun := edgeTo T d
  invFun := edgeFrom T d
  left_inv e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
    · have eq := DiscardResult.fin_three i
      rcases eq with rfl | rfl | rfl <;> rfl
  right_inv e := by
    rcases e with ⟨a,i⟩
    cases a <;> try rfl
    all_goals cases DiscardResult.fin_one i; rfl
/-- Retained frame wires are fixed while the empty replacement carrier is removed. -/
theorem map_frame {h} (T : ContractionTree .atom (h+2)) (d : Nat) (v : (beforeFrame h).Vertex) :
    Port.map (vertices T d).toFun
      (Net.Replacement.host (before T d) (head T d) (filler _ _ (head_at T d).1 true)
        (Net.Expansion.host (beforeFrame h) (beforeFill T) v)) =
      Net.Expansion.host (afterFrame h) (afterFill T) v := by cases v <;> rfl

/-- The old tree's complete port attachment is preserved by the carrier bijection. -/
theorem map_tree {h} (T : ContractionTree .atom (h+2)) (d : Nat) (v : T.net.Vertex) :
    Port.map (vertices T d).toFun
      (Net.Replacement.host (before T d) (head T d) (filler _ _ (head_at T d).1 true)
        (beforeLeftVertex T d v)) = afterLeftVertex T d v := by
  cases v with
  | internal v => rfl
  | input i => exact map_frame T d ((beforeFrame h).sourcePort .tree i)
  | output i => exact map_frame T d ((beforeFrame h).targetPort .tree i)

/-- Replacing just the comparison edge gives the complete original true-result graph. -/
noncomputable def replacement_iso {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Net.Iso (replaced T d) (after T d) where
  vertices := vertices T d
  edges := edges T d
  internal_label v := by
    rcases v with (v | ⟨a,v⟩) | v
    · rfl
    · cases a <;> first | rfl | exact nomatch v
    · exact nomatch v
  edge_label e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
    · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> rfl
  source e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      · exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      · change (((T.net.source i).map (beforeLeftVertex T d)).map
          (Net.Replacement.host (before T d) (head T d) (filler _ _ (head_at T d).1 true))).map
          (Port.map (vertices T d).toFun) = (T.net.source i).map (afterLeftVertex T d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_tree T d v)
    · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> cases d <;> rfl
  target e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      · exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      · change (((T.net.target i).map (beforeLeftVertex T d)).map
          (Net.Replacement.host (before T d) (head T d) (filler _ _ (head_at T d).1 true))).map
          (Port.map (vertices T d).toFun) = (T.net.target i).map (afterLeftVertex T d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_tree T d v)
    · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> cases d <;> rfl

/-- The original true comparison successor is canonical, including its resumed token. -/
noncomputable def canonical_local {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Combined.StateIso (canonical (before T d) (head T d) (head_at T d).1 (inputPort h 0) true)
      ⟨after T d,(.search,inputPort h 0)⟩ := ⟨DeepIso.ofIso (replacement_iso T d),rfl,rfl⟩
end Same
end Hypernets.Copying.AtomEquality
