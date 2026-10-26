import Hypernets.Copying.DereferenceMatch

/-! The canonical read construction commutes with recursive renaming and contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference.Match
open Graph Combined

noncomputable def graft_rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    {v} (m : Match G v) : DeepIso m.grafted (m.map (MatchEmbedding.ofDeepIso f)).grafted := by
  let n := m.map (MatchEmbedding.ofDeepIso f)
  let raw := f.plugHost m.headEdge (labelEquiv_input d (f.edge_label m.headEdge))
    (labelEquiv_output d (f.edge_label m.headEdge)) (labelEquiv_refl d) m.filler
  refine {
    vertices := raw.vertices
    edges := raw.edges
    internal_label := raw.internal_label
    edge_label := ?_
    source := ?_
    target := ?_ }
  · intro e; cases e with
    | inl e => exact f.edge_label e.val
    | inr e => exact labelEquiv_refl d _
  · intro e; cases e with
    | inl e => exact raw.source (.inl e)
    | inr e =>
      change ((((ReadStub.net d).source e).map (Port.cast _ _)).map
        (Net.Replacement.insert G m.headEdge m.filler)).map (Port.map raw.vertices.toFun) =
        (((ReadStub.net d).source e).map (Port.cast _ _)).map
          (Net.Replacement.insert H n.headEdge n.filler)
      simp only [List.map_map]
      apply List.map_congr_left
      intro x _
      have hx := Net.HostPlug.map_insert f m.headEdge
        (labelEquiv_input d (f.edge_label m.headEdge)) (labelEquiv_output d (f.edge_label m.headEdge))
        m.filler (Port.cast (by rw [m.head.1,primitive_input]; rfl)
          (by rw [m.head.1,primitive_output]; rfl) x)
      cases x <;> exact hx
  · intro e; cases e with
    | inl e => exact raw.target (.inl e)
    | inr e =>
      change ((((ReadStub.net d).target e).map (Port.cast _ _)).map
        (Net.Replacement.insert G m.headEdge m.filler)).map (Port.map raw.vertices.toFun) =
        (((ReadStub.net d).target e).map (Port.cast _ _)).map
          (Net.Replacement.insert H n.headEdge n.filler)
      simp only [List.map_map]
      apply List.map_congr_left
      intro x _
      have hx := Net.HostPlug.map_insert f m.headEdge
        (labelEquiv_input d (f.edge_label m.headEdge)) (labelEquiv_output d (f.edge_label m.headEdge))
        m.filler (Port.cast (by rw [m.head.1,primitive_input]; rfl)
          (by rw [m.head.1,primitive_output]; rfl) x)
      cases x <;> exact hx

noncomputable def canonical_rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    {v} (m : Match G v) : StateIso m.canonical (m.map (MatchEmbedding.ofDeepIso f)).canonical := by
  let n := m.map (MatchEmbedding.ofDeepIso f)
  exact TargetSwap.state_congr (graft_rename f m) m.fresh m.retained
    m.fresh_not_input m.retained_not_input m.endpoints_typed n.fresh n.retained
    n.fresh_not_input n.retained_not_input n.endpoints_typed rfl
    (Net.HostPlug.map_host f m.headEdge (labelEquiv_input d (f.edge_label m.headEdge)) (labelEquiv_output d (f.edge_label m.headEdge)) m.filler m.contents)
    _ _ (Net.HostPlug.map_host f m.headEdge (labelEquiv_input d (f.edge_label m.headEdge)) (labelEquiv_output d (f.edge_label m.headEdge)) m.filler v)
noncomputable def canonical_plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    {G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole))}
    {v} (m : Match G v) :
    StateIso (m.map (MatchEmbedding.plug C hole G)).canonical (plugState C hole m.canonical) := by
  let n := m.map (MatchEmbedding.plug C hole G)
  let iso := DeepIso.ofIso (C.plug_assoc hole G m.headEdge m.filler)
  let a := Net.Replacement.insert C hole m.grafted m.fresh
  let b := Net.Replacement.insert C hole m.grafted m.retained
  have na : ¬ a.IsInput := TargetSwap.embedded_not_input (MatchEmbedding.plug C hole m.grafted) m.fresh_not_input
  have nb : ¬ b.IsInput := TargetSwap.embedded_not_input (MatchEmbedding.plug C hole m.grafted) m.retained_not_input
  have typed : (C.plug hole m.grafted).vertexLabel a = (C.plug hole m.grafted).vertexLabel b :=
    (Net.Replacement.insert_label C hole m.grafted m.fresh).trans
      (m.endpoints_typed.trans (Net.Replacement.insert_label C hole m.grafted m.retained).symm)
  have first : StateIso n.canonical (TargetSwap.state (C.plug hole m.grafted) a b na nb typed
      (Net.Replacement.insert C hole m.grafted (Net.Replacement.host G m.headEdge m.filler v))) :=
    TargetSwap.state_congr iso n.fresh n.retained n.fresh_not_input n.retained_not_input n.endpoints_typed
      a b na nb typed rfl (Net.PlugAssoc.map_middle C hole G m.headEdge m.filler m.contents)
      _ _ (Net.PlugAssoc.map_middle C hole G m.headEdge m.filler v)
  exact first.trans (TargetSwap.state_plug C hole m.grafted m.fresh m.retained
    m.fresh_not_input m.retained_not_input m.endpoints_typed na nb typed _)
/-- Actual simultaneous expansion commutes with the whole read update and its resumed token. -/
noncomputable def canonical_expand_result {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e) {v w}
    (m : Match (F hole) v) (result : StateIso m.canonical ⟨K hole,(.search,w)⟩) :
    StateIso (m.map (MatchEmbedding.expand C F hole)).canonical
      ⟨C.expand K,(.search,Net.Expansion.insert C K hole w)⟩ := by
  let n := m.map (MatchEmbedding.expand C F hole)
  let P := Net.ExpansionPlug.family C F hole m.headEdge m.filler
  have eq : m.grafted = P hole := (Net.ExpansionPlug.family_same C F hole m.headEdge m.filler).symm
  let cv := cast (congrArg (fun G => G.Vertex) eq)
  let a := cv m.fresh
  let b := cv m.retained
  let token := cv (Net.Replacement.host (F hole) m.headEdge m.filler v)
  have na : ¬ a.IsInput := TargetSwap.cast_not_input eq m.fresh_not_input
  have nb : ¬ b.IsInput := TargetSwap.cast_not_input eq m.retained_not_input
  have typed : (P hole).vertexLabel a = (P hole).vertexLabel b := TargetSwap.cast_typed eq m.endpoints_typed
  have component : StateIso (TargetSwap.state (P hole) a b na nb typed token) ⟨K hole,(.search,w)⟩ :=
    (TargetSwap.state_cast eq m.fresh m.retained m.fresh_not_input m.retained_not_input
      m.endpoints_typed _).trans result
  let a' := Net.Expansion.insert C P hole a
  let b' := Net.Expansion.insert C P hole b
  have na' : ¬ a'.IsInput := TargetSwap.embedded_not_input (MatchEmbedding.expand C P hole) na
  have nb' : ¬ b'.IsInput := TargetSwap.embedded_not_input (MatchEmbedding.expand C P hole) nb
  have typed' : (C.expand P).vertexLabel a' = (C.expand P).vertexLabel b' :=
    (Net.Expansion.insert_label C P hole a).trans (typed.trans (Net.Expansion.insert_label C P hole b).symm)
  let iso := DeepIso.ofIso (Net.ExpansionPlug.iso C F hole m.headEdge m.filler)
  have first : StateIso n.canonical (TargetSwap.state (C.expand P) a' b' na' nb' typed'
      (Net.Expansion.insert C P hole token)) :=
    TargetSwap.state_congr iso n.fresh n.retained n.fresh_not_input n.retained_not_input n.endpoints_typed
      a' b' na' nb' typed'
      (Net.ExpansionPlug.map_inserted C F hole m.headEdge m.filler (.internal (0 : Fin 3)))
      (Net.ExpansionPlug.map_component C F hole m.headEdge m.filler m.contents)
      _ _ (Net.ExpansionPlug.map_component C F hole m.headEdge m.filler v)
  exact first.trans (TargetSwap.state_expand_result C P K hole
    (fun e ne => (Net.ExpansionPlug.family_other C F hole m.headEdge m.filler e ne).trans (others e ne))
    a b na nb typed na' nb' typed' component)
end Hypernets.Copying.Dereference.Match
