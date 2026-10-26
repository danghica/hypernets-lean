import Hypernets.Copying.TargetSwap

/-! Target exchange commutes with arbitrary typed attachment, without injective boundaries. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TargetSwap
open Graph

/-- Recursive renaming preserves target-only exchange and all original edge occurrences. -/
noncomputable def rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    (a b : G.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (eq : G.vertexLabel a = G.vertexLabel b)
    (na' : ¬ (Port.map f.vertices.toFun a).IsInput) (nb' : ¬ (Port.map f.vertices.toFun b).IsInput)
    (eq' : H.vertexLabel (Port.map f.vertices.toFun a) = H.vertexLabel (Port.map f.vertices.toFun b)) :
    DeepIso (net G a b na nb eq) (net H (Port.map f.vertices.toFun a) (Port.map f.vertices.toFun b) na' nb' eq') where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label := f.edge_label
  source := f.source
  target e := by
    change ((G.target e).map (exchange a b)).map (Port.map f.vertices.toFun) =
      (H.target (f.edges.toFun e)).map (exchange (Port.map f.vertices.toFun a) (Port.map f.vertices.toFun b))
    rw [← f.target,List.map_map,List.map_map]
    exact List.map_congr_left (fun x _ => (exchange_map (Port.map f.vertices.toFun) a b x
      (fun h => (Port.bijection f.vertices).injective h) (fun h => (Port.bijection f.vertices).injective h)).symm)

/-- Targets of a retained host edge cannot alias a non-input target of the inserted component. -/
theorem host_target_ne {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole)))
    {e : C.Edge} (ne : e ≠ hole) {v : C.Vertex} (mem : v ∈ C.target e)
    {a : G.Vertex} (na : ¬ a.IsInput) :
    Net.Replacement.host C hole G v ≠ Net.Replacement.insert C hole G a := by
  intro eq
  obtain ⟨i,_,h⟩ := Net.Replacement.insert_target_host C hole G na eq.symm
  exact ne (C.target_unique mem (h ▸ C.targetPort_mem hole i))

/-- Changing target incidences does not change the component's boundary attachment map. -/
theorem insert_plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole)))
    (a b : G.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (eq : G.vertexLabel a = G.vertexLabel b) (v : G.Vertex) :
    Net.Replacement.insert C hole (net G a b na nb eq) v = Net.Replacement.insert C hole G v := by
  cases v <;> rfl

/-- Exchanging two inserted target ports is the same graph as inserting the exchanged filler. -/
noncomputable def plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole)))
    (a b : G.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (eq : G.vertexLabel a = G.vertexLabel b)
    (na' : ¬ (Net.Replacement.insert C hole G a).IsInput)
    (nb' : ¬ (Net.Replacement.insert C hole G b).IsInput)
    (eq' : (C.plug hole G).vertexLabel (Net.Replacement.insert C hole G a) =
      (C.plug hole G).vertexLabel (Net.Replacement.insert C hole G b)) :
    Net.Iso (net (C.plug hole G) (Net.Replacement.insert C hole G a) (Net.Replacement.insert C hole G b) na' nb' eq')
      (C.plug hole (net G a b na nb eq)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := by cases e <;> rfl
  source e := by
    change ((C.plug hole G).source e).map (Port.map id) = _
    simp only [Port.map_id_fun,List.map_id_fun]
    cases e with
    | inl e => rfl
    | inr e =>
      exact List.map_congr_left (fun v _ => (insert_plug C hole G a b na nb eq v).symm)
  target e := by
    change (((C.plug hole G).target e).map
      (exchange (Net.Replacement.insert C hole G a) (Net.Replacement.insert C hole G b))).map (Port.map id) = _
    simp only [Port.map_id_fun,List.map_id_fun]
    cases e with
    | inl e =>
      change ((C.target e.val).map (Net.Replacement.host C hole G)).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v hv => exchange_other (host_target_ne C hole G e.property hv na)
        (host_target_ne C hole G e.property hv nb))
    | inr e =>
      change ((G.target e).map (Net.Replacement.insert C hole G)).map _ =
        ((G.target e).map (exchange a b)).map (Net.Replacement.insert C hole (net G a b na nb eq))
      rw [List.map_map,List.map_map]
      apply List.map_congr_left
      intro v hv
      simp only [Function.comp_apply,insert_plug]
      exact exchange_map (Net.Replacement.insert C hole G) a b v
        (Net.Replacement.insert_target_injective C hole G (G.target_not_input hv) na)
        (Net.Replacement.insert_target_injective C hole G (G.target_not_input hv) nb)
end Hypernets.Copying.TargetSwap
