import Hypernets.Copying.TargetSwapLocality

/-! Target exchange through simultaneous expansion, with unchanged component carriers. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TargetSwap
open Graph

/-- Only the selected component exchanges its two ports; every other component uses identity. -/
noncomputable def componentPermutation {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (e : C.Edge) : Bijection (F e).Vertex (F e).Vertex := by
  classical
  exact if eq : e = hole then by subst e; exact permutation a b else Bijection.refl _

theorem component_input {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (e : C.Edge) (v : (F e).Vertex) :
    ((componentPermutation C F hole a b e).toFun v).IsInput ↔ v.IsInput := by
  classical
  by_cases eq : e = hole
  · subst e; simpa [componentPermutation,permutation] using input_iff na nb v
  · simp [componentPermutation,eq,Bijection.refl]

theorem component_typed {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (same : (F hole).vertexLabel a = (F hole).vertexLabel b)
    (e : C.Edge) (v : (F e).Vertex) :
    (F e).vertexLabel ((componentPermutation C F hole a b e).toFun v) = (F e).vertexLabel v := by
  classical
  by_cases eq : e = hole
  · subst e; simpa [componentPermutation,permutation] using typed same v
  · simp [componentPermutation,eq,Bijection.refl]

/-- Reindexing, rather than selecting graphs by a dependent conditional, retains literal carriers. -/
@[reducible] noncomputable def family {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (same : (F hole).vertexLabel a = (F hole).vertexLabel b) (e : C.Edge) :
    Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)) :=
  reindex (F e) (componentPermutation C F hole a b e)
    (component_input C F hole a b na nb e) (component_typed C F hole a b same e)

theorem family_same {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (same : (F hole).vertexLabel a = (F hole).vertexLabel b) :
    family C F hole a b na nb same hole = net (F hole) a b na nb same := by
  simp [family,componentPermutation,net]

theorem family_other {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (same : (F hole).vertexLabel a = (F hole).vertexLabel b) (e : C.Edge) (ne : e ≠ hole) :
    family C F hole a b na nb same e = F e := by
  simp only [family,componentPermutation,dite_eq_right ne]
  exact reindex_refl (F e)

/-- The family keeps the original component insertion maps on all ports. -/
theorem insert_family {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (same : (F hole).vertexLabel a = (F hole).vertexLabel b) (e : C.Edge) (v : (F e).Vertex) :
    Net.Expansion.insert C (family C F hole a b na nb same) e v = Net.Expansion.insert C F e v := by
  cases v <;> rfl

/-- The complete expanded graph is unchanged except for the selected component's target exchange. -/
noncomputable def expand {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (same : (F hole).vertexLabel a = (F hole).vertexLabel b)
    (na' : ¬ (Net.Expansion.insert C F hole a).IsInput)
    (nb' : ¬ (Net.Expansion.insert C F hole b).IsInput)
    (same' : (C.expand F).vertexLabel (Net.Expansion.insert C F hole a) =
      (C.expand F).vertexLabel (Net.Expansion.insert C F hole b)) :
    Net.Iso (net (C.expand F) (Net.Expansion.insert C F hole a) (Net.Expansion.insert C F hole b) na' nb' same')
      (C.expand (family C F hole a b na nb same)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := rfl
  source e := by
    change ((C.expand F).source e).map (Port.map id) = _
    simp only [Port.map_id_fun,List.map_id_fun]
    exact List.map_congr_left (fun v _ => (insert_family C F hole a b na nb same e.1 v).symm)
  target e := by
    classical
    change (((C.expand F).target e).map
      (exchange (Net.Expansion.insert C F hole a) (Net.Expansion.insert C F hole b))).map (Port.map id) = _
    simp only [Port.map_id_fun,List.map_id_fun]
    rcases e with ⟨c,e⟩
    by_cases eq : c = hole
    · subst c
      change (((F hole).target e).map (Net.Expansion.insert C F hole)).map _ =
        (((F hole).target e).map (componentPermutation C F hole a b hole).toFun).map (Net.Expansion.insert C (family C F hole a b na nb same) hole)
      simp only [componentPermutation,dite_true,permutation,List.map_map]
      apply List.map_congr_left
      intro v hv
      simp only [Function.comp_apply,insert_family]
      exact exchange_map (Net.Expansion.insert C F hole) a b v
        (Net.Expansion.insert_target_injective C F hole ((F hole).target_not_input hv) na)
        (Net.Expansion.insert_target_injective C F hole ((F hole).target_not_input hv) nb)
    · change (((F c).target e).map (Net.Expansion.insert C F c)).map _ =
        (((F c).target e).map (componentPermutation C F hole a b c).toFun).map (Net.Expansion.insert C (family C F hole a b na nb same) c)
      simp only [componentPermutation,dite_eq_right eq,Bijection.refl,List.map_id_fun,List.map_map]
      apply List.map_congr_left
      intro v hv
      simp only [Function.comp_apply,insert_family]
      exact exchange_other
        (fun h => eq (Net.Expansion.target_owner C F ((F c).target_not_input hv) na h))
        (fun h => eq (Net.Expansion.target_owner C F ((F c).target_not_input hv) nb h))
end Hypernets.Copying.TargetSwap
