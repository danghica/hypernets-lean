import Hypernets.Graph.PlugAssociativity

/-! Independent shallow substitutions commute, including cyclic attachments. -/
namespace Hypernets.Graph.Net
universe u
namespace PlugInterchange
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O) (e f : C.Edge) (ne : f ≠ e)
    (H : Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))
    (K : Net σ (σ.input (C.edgeLabel f)) (σ.output (C.edgeLabel f)))

def vertices : Bijection ((C.Internal ⊕ H.Internal) ⊕ K.Internal)
    ((C.Internal ⊕ K.Internal) ⊕ H.Internal) where
  toFun | .inl (.inl v) => .inl (.inl v) | .inl (.inr v) => .inr v | .inr v => .inl (.inr v)
  invFun | .inl (.inl v) => .inl (.inl v) | .inl (.inr v) => .inr v | .inr v => .inl (.inr v)
  left_inv v := by rcases v with (v | v) | v <;> rfl
  right_inv v := by rcases v with (v | v) | v <;> rfl

def edges : Bijection (Replacement.Edge (C.plug e H) (.inl ⟨f,ne⟩) K)
    (Replacement.Edge (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H) where
  toFun
    | .inl ⟨.inl x,h⟩ => .inl ⟨.inl ⟨x.val,fun eq => h (by cases x; cases eq; rfl)⟩,
        fun eq => x.property (congrArg (fun y => y.val) (Sum.inl.inj eq))⟩
    | .inl ⟨.inr x,_⟩ => .inr x
    | .inr x => .inl ⟨.inr x,by intro eq; cases eq⟩
  invFun
    | .inl ⟨.inl x,h⟩ => .inl ⟨.inl ⟨x.val,fun eq => h (by cases x; cases eq; rfl)⟩,
        fun eq => x.property (congrArg (fun y => y.val) (Sum.inl.inj eq))⟩
    | .inl ⟨.inr x,_⟩ => .inr x
    | .inr x => .inl ⟨.inr x,by intro eq; cases eq⟩
  left_inv v := by rcases v with ⟨v | v,h⟩ | v <;> rfl
  right_inv v := by rcases v with ⟨v | v,h⟩ | v <;> rfl

theorem sourcePort_retained (i) :
    (C.plug e H).sourcePort (.inl ⟨f,ne⟩) i = Replacement.host C e H (C.sourcePort f i) := by
  simp [sourcePort,plug,Replacement.source,List.getElem_map]

theorem targetPort_retained (i) :
    (C.plug e H).targetPort (.inl ⟨f,ne⟩) i = Replacement.host C e H (C.targetPort f i) := by
  simp [targetPort,plug,Replacement.target,List.getElem_map]

theorem map_host (v : C.Vertex) :
    Port.map (vertices C e f H K).toFun
      (Replacement.host (C.plug e H) (.inl ⟨f,ne⟩) K (Replacement.host C e H v)) =
    Replacement.host (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H (Replacement.host C f K v) := by
  cases v <;> rfl

theorem map_first (v : H.Vertex) :
    Port.map (vertices C e f H K).toFun
      (Replacement.host (C.plug e H) (.inl ⟨f,ne⟩) K (Replacement.insert C e H v)) =
    Replacement.insert (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H v := by
  cases v with
  | internal => rfl
  | input i =>
      change _ = Replacement.host (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H ((C.plug f K).sourcePort (.inl ⟨e,Ne.symm ne⟩) i)
      exact (map_host C e f ne H K _).trans
        (congrArg (Replacement.host (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H)
          (sourcePort_retained C f e (Ne.symm ne) K i).symm)
  | output i =>
      change _ = Replacement.host (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H ((C.plug f K).targetPort (.inl ⟨e,Ne.symm ne⟩) i)
      exact (map_host C e f ne H K _).trans
        (congrArg (Replacement.host (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H)
          (targetPort_retained C f e (Ne.symm ne) K i).symm)

theorem map_second (v : K.Vertex) :
    Port.map (vertices C e f H K).toFun (Replacement.insert (C.plug e H) (.inl ⟨f,ne⟩) K v) =
    Replacement.host (C.plug f K) (.inl ⟨e,Ne.symm ne⟩) H (Replacement.insert C f K v) := by
  cases v with
  | internal => rfl
  | input i =>
      change Port.map (vertices C e f H K).toFun (Replacement.host (C.plug e H) (.inl ⟨f,ne⟩) K ((C.plug e H).sourcePort (.inl ⟨f,ne⟩) i)) = _
      exact (congrArg (fun v => Port.map (vertices C e f H K).toFun
        (Replacement.host (C.plug e H) (.inl ⟨f,ne⟩) K v))
        (sourcePort_retained C e f ne H i)).trans (map_host C e f ne H K _)
  | output i =>
      change Port.map (vertices C e f H K).toFun (Replacement.host (C.plug e H) (.inl ⟨f,ne⟩) K ((C.plug e H).targetPort (.inl ⟨f,ne⟩) i)) = _
      exact (congrArg (fun v => Port.map (vertices C e f H K).toFun
        (Replacement.host (C.plug e H) (.inl ⟨f,ne⟩) K v))
        (targetPort_retained C e f ne H i)).trans (map_host C e f ne H K _)

/-- Substitutions at distinct retained host edges commute up to an explicit isomorphism. -/
noncomputable def iso :
    Iso ((C.plug e H).plug (.inl ⟨f,ne⟩) K)
      ((C.plug f K).plug (.inl ⟨e,Ne.symm ne⟩) H) where
  vertices := vertices C e f H K
  edges := edges C e f ne H K
  internal_label v := by rcases v with (v | v) | v <;> rfl
  edge_label v := by rcases v with ⟨v | v,h⟩ | v <;> rfl
  source x := by
    rcases x with ⟨x | x,h⟩ | x
    · change (((C.source x.val).map _).map _).map _ = _
      simp only [plug,Replacement.source,edges,Net.Vertex,Replacement.Vertex,
        Replacement.edgeLabel,List.map_map]
      exact List.map_congr_left (fun v _ => map_host C e f ne H K v)
    · change (((H.source x).map _).map _).map _ = _
      simp only [plug,Replacement.source,edges,Net.Vertex,Replacement.Vertex,
        Replacement.edgeLabel,List.map_map]
      exact List.map_congr_left (fun v _ => map_first C e f ne H K v)
    · change ((K.source x).map _).map _ = _
      simp only [plug,Replacement.source,edges,Net.Vertex,Replacement.Vertex,
        Replacement.edgeLabel,List.map_map]
      exact (List.map_map ..).trans (List.map_congr_left (fun v _ => map_second C e f ne H K v))
  target x := by
    rcases x with ⟨x | x,h⟩ | x
    · change (((C.target x.val).map _).map _).map _ = _
      simp only [plug,Replacement.target,edges,Net.Vertex,Replacement.Vertex,
        Replacement.edgeLabel,List.map_map]
      exact List.map_congr_left (fun v _ => map_host C e f ne H K v)
    · change (((H.target x).map _).map _).map _ = _
      simp only [plug,Replacement.target,edges,Net.Vertex,Replacement.Vertex,
        Replacement.edgeLabel,List.map_map]
      exact List.map_congr_left (fun v _ => map_first C e f ne H K v)
    · change ((K.target x).map _).map _ = _
      simp only [plug,Replacement.target,edges,Net.Vertex,Replacement.Vertex,
        Replacement.edgeLabel,List.map_map]
      exact (List.map_map ..).trans (List.map_congr_left (fun v _ => map_second C e f ne H K v))

end PlugInterchange
end Hypernets.Graph.Net
