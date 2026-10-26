import Hypernets.Copying.DereferenceCanonicalTransport

/-! Explicit comparison between canonical read rewiring and the original Figure 19(b). -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference.Replacement
open Graph

noncomputable abbrev replaced {h} (T : ContractionTree .atom (h+1)) (d : Nat) :=
  (localMatch T d).canonical.1

def vertexTo {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (replaced T d).Internal → (after T d).Internal
  | .inl (.inl i) => .inl i.castSucc
  | .inl (.inr ⟨.tree,v⟩) => .inr ⟨.tree,v⟩
  | .inl (.inr ⟨.reader,v⟩) => nomatch v
  | .inl (.inr ⟨.inst,v⟩) => nomatch v
  | .inl (.inr ⟨.store,v⟩) => nomatch v
  | .inr i => if eq : i.val = 0 then .inl (3 : Fin 4) else .inr ⟨.share,⟨i.val-1,by have := i.isLt; omega⟩⟩

def vertexFrom {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (after T d).Internal → (replaced T d).Internal
  | .inl i => if small : i.val < 3 then .inl (.inl ⟨i.val,small⟩) else .inr (0 : Fin 3)
  | .inr ⟨.tree,v⟩ => .inl (.inr ⟨.tree,v⟩)
  | .inr ⟨.share,i⟩ => .inr ⟨i.val+1,by have := i.isLt; omega⟩
  | .inr ⟨.discard,v⟩ => nomatch v
  | .inr ⟨.inst,v⟩ => nomatch v
  | .inr ⟨.store,v⟩ => nomatch v

def vertices {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Bijection (replaced T d).Internal (after T d).Internal where
  toFun := vertexTo T d
  invFun := vertexFrom T d
  left_inv v := by
    rcases v with (v | ⟨e,v⟩) | v
    · rcases DiscardResult.fin_three v with rfl | rfl | rfl <;> rfl
    · cases e <;> first | rfl | exact nomatch v
    · rcases DiscardResult.fin_three v with rfl | rfl | rfl <;> rfl
  right_inv v := by
    rcases v with v | ⟨e,v⟩
    · rcases ReadStub.fin_four v with rfl | rfl | rfl | rfl <;> rfl
    · cases e <;> first | rfl | exact nomatch v

def edgeTo {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (replaced T d).Edge → (after T d).Edge
  | .inl ⟨⟨.reader,i⟩,ne⟩ => False.elim (ne (by cases DiscardResult.fin_one i; rfl))
  | .inl ⟨⟨.inst,i⟩,_⟩ => ⟨.inst,i⟩
  | .inl ⟨⟨.tree,i⟩,_⟩ => ⟨.tree,i⟩
  | .inl ⟨⟨.store,i⟩,_⟩ => ⟨.store,i⟩
  | .inr i => if zero : i.val = 0 then ⟨.discard,(0 : Fin 1)⟩ else ⟨.share,⟨i.val-1,by have := i.isLt; omega⟩⟩

def edgeFrom {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    (after T d).Edge → (replaced T d).Edge
  | ⟨.discard,_⟩ => .inr (0 : Fin 4)
  | ⟨.share,i⟩ => .inr ⟨i.val+1,by have := i.isLt; omega⟩
  | ⟨.inst,i⟩ => .inl ⟨⟨.inst,i⟩,by intro eq; cases eq⟩
  | ⟨.tree,i⟩ => .inl ⟨⟨.tree,i⟩,by intro eq; cases eq⟩
  | ⟨.store,i⟩ => .inl ⟨⟨.store,i⟩,by intro eq; cases eq⟩

def edges {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Bijection (replaced T d).Edge (after T d).Edge where
  toFun := edgeTo T d
  invFun := edgeFrom T d
  left_inv e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
    · rcases ReadStub.fin_four i with rfl | rfl | rfl | rfl <;> rfl
  right_inv e := by
    rcases e with ⟨a,i⟩
    cases a <;> try rfl
    · cases DiscardResult.fin_one i; rfl

/-- Every port of the matched atom tree retains its original attachment. -/
theorem map_tree {h} (T : ContractionTree .atom (h+1)) (d : Nat) (v : T.net.Vertex) :
    Port.map (vertices T d).toFun
      (Net.Replacement.host (before T d) (localMatch T d).headEdge (localMatch T d).filler
        (beforeTreeVertex T d v)) = afterTreeVertex T d v := by
  cases v with
  | internal v => rfl
  | output i => cases DiscardResult.fin_one i; rfl
  | input i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [beforeTreeVertex,afterTreeVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,beforeFrame,afterFrame,
        beforeSource,afterSource,otherInputs,inputPort,Net.Replacement.host,
        Port.map,List.getElem_map]


/-- Tree targets cannot hit the retained external content port or the freshly inserted wire. -/
theorem exchange_tree {h} (T : ContractionTree .atom (h+1)) (d : Nat) (v : T.net.Vertex) :
    TargetSwap.exchange (localMatch T d).fresh (localMatch T d).retained
      (Net.Replacement.host (before T d) (localMatch T d).headEdge (localMatch T d).filler
        (beforeTreeVertex T d v)) =
      Net.Replacement.host (before T d) (localMatch T d).headEdge (localMatch T d).filler
        (beforeTreeVertex T d v) := by
  apply TargetSwap.exchange_other
  · change _ ≠ Port.internal (Sum.inr (0 : Fin 3))
    have avoid (x : (before T d).Vertex) :
        Net.Replacement.host (before T d) (localMatch T d).headEdge (localMatch T d).filler x ≠
          Port.internal (Sum.inr (0 : Fin 3)) := by cases x <;> simp [Net.Replacement.host,Port.map]
    exact avoid _
  · cases v with
    | internal v => intro eq; cases eq
    | output i => cases DiscardResult.fin_one i; intro eq; cases eq
    | input i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · intro eq; cases eq
      · simp [beforeTreeVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,beforeFrame,beforeSource,
          otherInputs,inputPort,Net.Replacement.host,Port.map,Match.retained,localMatch,
          List.getElem_map]

/-- A complete graph isomorphism, preserving every original atom-tree occurrence and
introducing exactly the canonical sharing tree, with its weakening and two contractions. -/
noncomputable def iso {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Net.Iso (replaced T d) (after T d) where
  vertices := vertices T d
  edges := edges T d
  internal_label v := by
    rcases v with (v | ⟨a,v⟩) | v
    · rcases DiscardResult.fin_three v with rfl | rfl | rfl <;> rfl
    · cases a <;> first | rfl | exact nomatch v
    · rcases DiscardResult.fin_three v with rfl | rfl | rfl <;> rfl
  edge_label e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
    · rcases ReadStub.fin_four i with rfl | rfl | rfl | rfl <;> rfl
  source e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a <;> try rfl
      · exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      · change (((T.net.source i).map (beforeTreeVertex T d)).map
          (Net.Replacement.host (before T d) (localMatch T d).headEdge (localMatch T d).filler)).map
          (Port.map (vertices T d).toFun) = (T.net.source i).map (afterTreeVertex T d)
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_tree T d v)
    · rcases ReadStub.fin_four i with rfl | rfl | rfl | rfl <;> rfl
  target e := by
    rcases e with ⟨⟨a,i⟩,ne⟩ | i
    · cases a with
      | reader => exact False.elim (ne (by cases DiscardResult.fin_one i; rfl))
      | inst =>
        cases DiscardResult.fin_one i
        change [Port.map (vertices T d).toFun
          (TargetSwap.exchange (Port.internal (Sum.inr (0 : Fin 3))) (Port.output 0)
            (Port.internal (Sum.inl (Sum.inl (1 : Fin 3)))))] = _
        rw [TargetSwap.exchange_other (by intro eq; cases eq) (by intro eq; cases eq)]
        rfl
      | store =>
        cases DiscardResult.fin_one i
        change [Port.map (vertices T d).toFun
          (TargetSwap.exchange (Port.internal (Sum.inr (0 : Fin 3))) (Port.output 0) (Port.output 0))] = _
        rw [TargetSwap.exchange_right]
        rfl
      | tree =>
        change ((((T.net.target i).map (beforeTreeVertex T d)).map
          (Net.Replacement.host (before T d) (localMatch T d).headEdge (localMatch T d).filler)).map
          (TargetSwap.exchange (localMatch T d).fresh (localMatch T d).retained)).map
          (Port.map (vertices T d).toFun) = (T.net.target i).map (afterTreeVertex T d)
        simp only [List.map_map]
        apply List.map_congr_left
        intro v _
        dsimp only [Function.comp_def]
        rw [exchange_tree]
        exact map_tree T d v
    · rcases ReadStub.fin_four i with rfl | rfl | rfl | rfl
      · change [Port.map (vertices T d).toFun
          (TargetSwap.exchange (Port.internal (Sum.inr (0 : Fin 3))) (Port.output 0)
            (Port.internal (Sum.inl (Sum.inl (0 : Fin 3)))))] = _
        rw [TargetSwap.exchange_other (by intro eq; cases eq) (by intro eq; cases eq)]
        rfl
      · change [Port.map (vertices T d).toFun
          (TargetSwap.exchange (Port.internal (Sum.inr (0 : Fin 3))) (Port.output 0)
            (Port.internal (Sum.inr (1 : Fin 3))))] = _
        rw [TargetSwap.exchange_other (by intro eq; cases eq) (by intro eq; cases eq)]
        rfl
      · change [Port.map (vertices T d).toFun
          (TargetSwap.exchange (Port.internal (Sum.inr (0 : Fin 3))) (Port.output 0)
            (Port.internal (Sum.inr (0 : Fin 3))))] = _
        rw [TargetSwap.exchange_left]
        rfl
      · change [Port.map (vertices T d).toFun
          (TargetSwap.exchange (Port.internal (Sum.inr (0 : Fin 3))) (Port.output 0)
            (Port.internal (Sum.inr (2 : Fin 3))))] = _
        rw [TargetSwap.exchange_other (by intro eq; cases eq) (by intro eq; cases eq)]
        rfl

noncomputable def canonical_local {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Combined.StateIso (localMatch T d).canonical ⟨after T d,(.search,inputPort h 0)⟩ :=
  ⟨DeepIso.ofIso (iso T d),rfl,rfl⟩
end Hypernets.Copying.Dereference.Replacement
