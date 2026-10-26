import Hypernets.Copying.EqualityReplacement

/-! Complete canonical replacement for the distinct-store equality branch. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Different
open Graph

def head {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Edge := ⟨.compare,(0 : Fin 1)⟩
theorem head_at {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    MatchEmbedding.HeadAt (before T U d) (inputPort n m 0) (head T U d) (.operation (.binary .atomEq)) :=
  ⟨rfl,List.mem_cons_self⟩

/-- Source of the local isomorphism, retaining the atom tree and store as host edges. -/
noncomputable abbrev replaced {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :=
  (canonical (before T U d) (head T U d) (head_at T U d).1 (inputPort n m 0) false).1

/-- No internal wire is deleted: only the vacuous replacement component is eliminated. -/
def vertexTo {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (replaced T U d).Internal → (after T U d).Internal
  | .inl (.inl v) => .inl v
  | .inl (.inr ⟨.tree,v⟩) => .inr ⟨.tree,v⟩
  | .inl (.inr ⟨.treeRight,v⟩) => .inr ⟨.treeRight,v⟩
  | .inl (.inr ⟨.compare,v⟩) => nomatch v
  | .inl (.inr ⟨.left,v⟩) => nomatch v
  | .inl (.inr ⟨.right,v⟩) => nomatch v
  | .inl (.inr ⟨.store,v⟩) => nomatch v
  | .inl (.inr ⟨.storeRight,v⟩) => nomatch v
  | .inr v => nomatch v

def vertexFrom {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Internal → (replaced T U d).Internal
  | .inl v => .inl (.inl v)
  | .inr ⟨.tree,v⟩ => .inl (.inr ⟨.tree,v⟩)
  | .inr ⟨.treeRight,v⟩ => .inl (.inr ⟨.treeRight,v⟩)
  | .inr ⟨.result,v⟩ => nomatch v
  | .inr ⟨.discardLeft,v⟩ => nomatch v
  | .inr ⟨.discardRight,v⟩ => nomatch v
  | .inr ⟨.left,v⟩ => nomatch v
  | .inr ⟨.right,v⟩ => nomatch v
  | .inr ⟨.store,v⟩ => nomatch v
  | .inr ⟨.storeRight,v⟩ => nomatch v

def vertices {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : Bijection (replaced T U d).Internal (after T U d).Internal where
  toFun := vertexTo T U d
  invFun := vertexFrom T U d
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
def edgeTo {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (replaced T U d).Edge → (after T U d).Edge
  | .inl ⟨⟨.compare,i⟩,ne⟩ => False.elim (ne (by have eq : i = (0 : Fin 1) := DiscardResult.fin_one i; cases eq; rfl))
  | .inl ⟨⟨.left,i⟩,_⟩ => ⟨.left,i⟩
  | .inl ⟨⟨.right,i⟩,_⟩ => ⟨.right,i⟩
  | .inl ⟨⟨.tree,i⟩,_⟩ => ⟨.tree,i⟩
  | .inl ⟨⟨.store,i⟩,_⟩ => ⟨.store,i⟩
  | .inl ⟨⟨.treeRight,i⟩,_⟩ => ⟨.treeRight,i⟩
  | .inl ⟨⟨.storeRight,i⟩,_⟩ => ⟨.storeRight,i⟩
  | .inr i => if i.val = 0 then ⟨.result,(0 : Fin 1)⟩ else
      if i.val = 1 then ⟨.discardLeft,(0 : Fin 1)⟩ else ⟨.discardRight,(0 : Fin 1)⟩

def edgeFrom {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge → (replaced T U d).Edge
  | ⟨.result,_⟩ => .inr (0 : Fin 3)
  | ⟨.discardLeft,_⟩ => .inr (1 : Fin 3)
  | ⟨.discardRight,_⟩ => .inr (2 : Fin 3)
  | ⟨.left,i⟩ => .inl ⟨⟨.left,i⟩,by intro eq; cases eq⟩
  | ⟨.right,i⟩ => .inl ⟨⟨.right,i⟩,by intro eq; cases eq⟩
  | ⟨.tree,i⟩ => .inl ⟨⟨.tree,i⟩,by intro eq; cases eq⟩
  | ⟨.store,i⟩ => .inl ⟨⟨.store,i⟩,by intro eq; cases eq⟩
  | ⟨.treeRight,i⟩ => .inl ⟨⟨.treeRight,i⟩,by intro eq; cases eq⟩
  | ⟨.storeRight,i⟩ => .inl ⟨⟨.storeRight,i⟩,by intro eq; cases eq⟩

def edges {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : Bijection (replaced T U d).Edge (after T U d).Edge where
  toFun := edgeTo T U d
  invFun := edgeFrom T U d
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
theorem map_frame {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (v : (beforeFrame n m).Vertex) :
    Port.map (vertices T U d).toFun
      (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false)
        (Net.Expansion.host (beforeFrame n m) (beforeFill T U) v)) =
      Net.Expansion.host (afterFrame n m) (afterFill T U) v := by cases v <;> rfl

/-- The old tree's complete port attachment is preserved by the carrier bijection. -/
theorem map_tree {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (v : T.net.Vertex) :
    Port.map (vertices T U d).toFun
      (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false)
        (beforeLeftVertex T U d v)) = afterLeftVertex T U d v := by
  cases v with
  | internal v => rfl
  | input i => exact map_frame T U d ((beforeFrame n m).sourcePort .tree i)
  | output i => exact map_frame T U d ((beforeFrame n m).targetPort .tree i)

/-- The second old tree's complete port attachment is preserved by the carrier bijection. -/
theorem map_right_tree {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (v : U.net.Vertex) :
    Port.map (vertices T U d).toFun
      (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false)
        (beforeRightVertex T U d v)) = afterRightVertex T U d v := by
  cases v with
  | internal v => rfl
  | input i => exact map_frame T U d ((beforeFrame n m).sourcePort .treeRight i)
  | output i => exact map_frame T U d ((beforeFrame n m).targetPort .treeRight i)

/-- Replacing just the comparison edge gives the complete original false-result graph. -/
noncomputable def replacement_iso {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Net.Iso (replaced T U d) (after T U d) where
  vertices := vertices T U d
  edges := edges T U d
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
      · change (((T.net.source i).map (beforeLeftVertex T U d)).map
          (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false))).map
          (Port.map (vertices T U d).toFun) = (T.net.source i).map (afterLeftVertex T U d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_tree T U d v)
      · change (((U.net.source i).map (beforeRightVertex T U d)).map
          (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false))).map
          (Port.map (vertices T U d).toFun) = (U.net.source i).map (afterRightVertex T U d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_right_tree T U d v)
    · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> cases d <;> rfl
  target e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      · exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      · change (((T.net.target i).map (beforeLeftVertex T U d)).map
          (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false))).map
          (Port.map (vertices T U d).toFun) = (T.net.target i).map (afterLeftVertex T U d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_tree T U d v)
      · change (((U.net.target i).map (beforeRightVertex T U d)).map
          (Net.Replacement.host (before T U d) (head T U d) (filler _ _ (head_at T U d).1 false))).map
          (Port.map (vertices T U d).toFun) = (U.net.target i).map (afterRightVertex T U d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_right_tree T U d v)
    · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> cases d <;> rfl

/-- The original false comparison successor is canonical, including its resumed token. -/
noncomputable def canonical_local {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Combined.StateIso (canonical (before T U d) (head T U d) (head_at T U d).1 (inputPort n m 0) false)
      ⟨after T U d,(.search,inputPort n m 0)⟩ := ⟨DeepIso.ofIso (replacement_iso T U d),rfl,rfl⟩
end Hypernets.Copying.AtomEquality.Different
