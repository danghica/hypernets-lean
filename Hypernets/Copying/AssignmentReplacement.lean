import Hypernets.Copying.AssignmentCanonicalTransport

/-! The original assignment reduct is the canonical target exchange and head replacement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph
namespace Replacement

noncomputable abbrev replaced {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :=
  (localMatch T G).canonical.1

def vertexTo {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (replaced T G).Internal → (after T G).Internal := by
  cases d
  all_goals exact fun
    | .inl (.inl v) => .inl v
    | .inl (.inr ⟨.tree,v⟩) => .inr ⟨.tree,v⟩
    | .inl (.inr ⟨.value,v⟩) => .inr ⟨.value,v⟩
    | .inl (.inr ⟨.assign,v⟩) => nomatch v
    | .inl (.inr ⟨.inst,v⟩) => nomatch v
    | .inl (.inr ⟨.store,v⟩) => nomatch v
    | .inr v => nomatch v

def vertexFrom {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (after T G).Internal → (replaced T G).Internal := by
  cases d
  all_goals exact fun
    | .inl v => .inl (.inl v)
    | .inr ⟨.tree,v⟩ => .inl (.inr ⟨.tree,v⟩)
    | .inr ⟨.value,v⟩ => .inl (.inr ⟨.value,v⟩)
    | .inr ⟨.discardInstance,v⟩ => nomatch v
    | .inr ⟨.inst,v⟩ => nomatch v
    | .inr ⟨.store,v⟩ => nomatch v
    | .inr ⟨.discardOld,v⟩ => nomatch v
    | .inr ⟨.unit,v⟩ => nomatch v

def vertices {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Bijection (replaced T G).Internal (after T G).Internal where
  toFun := vertexTo T G
  invFun := vertexFrom T G
  left_inv v := by
    cases d
    all_goals
      rcases v with (v | ⟨e,v⟩) | v
      · rfl
      · cases e <;> first | rfl | exact nomatch v
      · exact nomatch v
  right_inv v := by
    cases d
    all_goals
      rcases v with v | ⟨e,v⟩
      · rfl
      · cases e <;> first | rfl | exact nomatch v

def edgeTo {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (replaced T G).Edge → (after T G).Edge := by
  cases d
  all_goals exact fun
    | .inl ⟨⟨.assign,i⟩,ne⟩ => False.elim (ne (by cases DiscardResult.fin_one i; rfl))
    | .inl ⟨⟨.inst,i⟩,_⟩ => ⟨.inst,i⟩
    | .inl ⟨⟨.tree,i⟩,_⟩ => ⟨.tree,i⟩
    | .inl ⟨⟨.store,i⟩,_⟩ => ⟨.store,i⟩
    | .inl ⟨⟨.value,i⟩,_⟩ => ⟨.value,i⟩
    | .inr i => if i.val = 0 then ⟨.unit,(0 : Fin 1)⟩ else
        if i.val = 1 then ⟨.discardInstance,(0 : Fin 1)⟩ else ⟨.discardOld,(0 : Fin 1)⟩

def edgeFrom {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (after T G).Edge → (replaced T G).Edge := by
  cases d
  all_goals exact fun
    | ⟨.unit,_⟩ => .inr (0 : Fin 3)
    | ⟨.discardInstance,_⟩ => .inr (1 : Fin 3)
    | ⟨.discardOld,_⟩ => .inr (2 : Fin 3)
    | ⟨.inst,i⟩ => .inl ⟨⟨.inst,i⟩,by intro eq; cases eq⟩
    | ⟨.tree,i⟩ => .inl ⟨⟨.tree,i⟩,by intro eq; cases eq⟩
    | ⟨.store,i⟩ => .inl ⟨⟨.store,i⟩,by intro eq; cases eq⟩
    | ⟨.value,i⟩ => .inl ⟨⟨.value,i⟩,by intro eq; cases eq⟩

def edges {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Bijection (replaced T G).Edge (after T G).Edge where
  toFun := edgeTo T G
  invFun := edgeFrom T G
  left_inv e := by
    cases d
    all_goals
      rcases e with ⟨⟨a,i⟩,ne⟩ | i
      · cases a <;> try rfl
        exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> rfl
  right_inv e := by
    cases d
    all_goals
      rcases e with ⟨a,i⟩
      cases a <;> try rfl
      all_goals cases DiscardResult.fin_one i; rfl

/-- The canonical construction preserves every frame wire, including the new-value input. -/
theorem map_frame {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (v : (beforeFrame h O).Vertex) :
    Port.map (vertices T G).toFun
      (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler
        (Net.Expansion.host (beforePattern d h O) (beforeFill T G) v)) =
      Net.Expansion.host (afterPattern d h O) (afterFill T G) v := by
  cases d <;> cases v <;> rfl

theorem map_tree {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (v : T.net.Vertex) :
    Port.map (vertices T G).toFun
      (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler
        (beforeTreeVertex T G v)) = afterTreeVertex T G v := by
  cases d
  all_goals
    cases v with
    | internal v => rfl
    | input i => exact map_frame T G ((beforeFrame h O).sourcePort .tree i)
    | output i => exact map_frame T G ((beforeFrame h O).targetPort .tree i)

/-- The original value component's actual insertion map, including all of its boundary ports. -/
def beforeValueVertex {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    G.Vertex → (before T G).Vertex := by
  cases d <;> exact Net.Expansion.insert (beforePattern _ h O) (beforeFill T G) .value

theorem map_value {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (v : G.Vertex) :
    Port.map (vertices T G).toFun
      (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler
        (beforeValueVertex T G v)) = afterValueVertex T G v := by
  cases d
  all_goals
    cases v with
    | internal v => rfl
    | input i => exact map_frame T G ((beforeFrame h O).sourcePort .value i)
    | output i => exact map_frame T G ((beforeFrame h O).targetPort .value i)
/-- Canonical replacement leaves every non-head, non-store target list unchanged. -/
theorem retained_target {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (e : (before T G).Edge) (head : e ≠ (localMatch T G).headEdge) (store : e ≠ (localMatch T G).storeEdge) :
    (replaced T G).target (.inl ⟨e,head⟩) =
      ((before T G).target e).map
        (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler) := by
  change ((localMatch T G).swapped.target e).map _ = _
  rw [Match.swapped_other_target _ _ head store]

/-- A full graph isomorphism to the original assignment target, retaining the entire tree and value subgraph. -/
noncomputable def iso {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Net.Iso (replaced T G) (after T G) where
  vertices := vertices T G
  edges := edges T G
  internal_label v := by
    cases d
    all_goals
      rcases v with (v | ⟨a,v⟩) | v
      · rfl
      · cases a <;> first | rfl | exact nomatch v
      · exact nomatch v
  edge_label e := by
    cases d
    all_goals
      rcases e with ⟨⟨a,i⟩,ne⟩ | i
      · cases a <;> try rfl
        exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> rfl
  source e := by
    cases d
    all_goals
      rcases e with ⟨⟨a,i⟩,ne⟩ | i
      · cases a <;> try rfl
        · exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
        · change (((T.net.source i).map (beforeTreeVertex T G)).map
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler)).map
            (Port.map (vertices T G).toFun) = (T.net.source i).map (afterTreeVertex T G)
          simp only [List.map_map]
          exact List.map_congr_left (fun v _ => map_tree T G v)
        · change (((G.source i).map (beforeValueVertex T G)).map
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler)).map
            (Port.map (vertices T G).toFun) = (G.source i).map (afterValueVertex T G)
          simp only [List.map_map]
          exact List.map_congr_left (fun v _ => map_value T G v)
      · rcases DiscardResult.fin_three i with rfl | rfl | rfl <;> rfl
  target e := by
    cases d
    all_goals
      rcases e with ⟨⟨a,i⟩,ne⟩ | i
      · cases a with
        | assign => exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
        | inst =>
          change ((replaced T G).target (.inl ⟨⟨.inst,i⟩,ne⟩)).map _ = _
          rw [retained_target T G _ ne (by intro eq; cases eq)]
          rfl
        | tree =>
          change ((replaced T G).target (.inl ⟨⟨.tree,i⟩,ne⟩)).map _ = _
          rw [retained_target T G _ ne (by intro eq; cases eq)]
          change (((T.net.target i).map (beforeTreeVertex T G)).map
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler)).map
            (Port.map (vertices T G).toFun) = (T.net.target i).map (afterTreeVertex T G)
          simp only [List.map_map]
          exact List.map_congr_left (fun v _ => map_tree T G v)
        | store =>
          cases DiscardResult.fin_one i
          change (((localMatch T G).swapped.target (localMatch T G).storeEdge).map
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler)).map _ = _
          rw [Match.swapped_store_target]
          rfl
        | value =>
          change ((replaced T G).target (.inl ⟨⟨.value,i⟩,ne⟩)).map _ = _
          rw [retained_target T G _ ne (by intro eq; cases eq)]
          change (((G.target i).map (beforeValueVertex T G)).map
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler)).map
            (Port.map (vertices T G).toFun) = (G.target i).map (afterValueVertex T G)
          simp only [List.map_map]
          exact List.map_congr_left (fun v _ => map_value T G v)
      · rcases DiscardResult.fin_three i with rfl | rfl | rfl
        · rfl
        · change [Port.map (vertices T G).toFun
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler
              ((localMatch T G).swapped.targetPort (localMatch T G).headEdge ⟨0,by change 0 < 2; decide⟩))] = _
          rw [Match.swapped_first]
          rfl
        · change [Port.map (vertices T G).toFun
            (Net.Replacement.host (localMatch T G).swapped (localMatch T G).headEdge (localMatch T G).filler
              ((localMatch T G).swapped.targetPort (localMatch T G).headEdge ⟨1,by change 1 < 2; decide⟩))] = _
          rw [Match.swapped_second]
          rfl

/-- The complete original reduct and resumed token agree with canonical write construction. -/
noncomputable def canonical_local {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Combined.StateIso (localMatch T G).canonical ⟨after T G,(.search,inputPort h O 0)⟩ := by
  refine ⟨DeepIso.ofIso (iso T G),rfl,?_⟩
  cases d <;> rfl
end Replacement
end Hypernets.Copying.Assignment
