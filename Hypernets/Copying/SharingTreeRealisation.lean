import Hypernets.Copying.SharingTreeExpansion

/-! Recover the paper's primitive contraction trees from expanded sharing
contexts without changing any vertex, edge or ordered incidence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- The actual sharing-only hypernet property, before erasing its allowance. -/
structure SharingTreeGraph {d : Nat} (s : ShareSort) (m : Nat)
    (G : Hypernet d (List.replicate m s.wire) [s.wire]) : Prop where
  labels : ∀ e, G.edgeLabel e = primitiveLabel d (.weakening s) ∨
    G.edgeLabel e = primitiveLabel d (.contraction s)
  acyclic : ∀ {es}, G.Path es → es.Nodup

namespace SharingTreeGraph
variable {d : Nat} {s : ShareSort} {m : Nat}
    {G : Hypernet d (List.replicate m s.wire) [s.wire]} (h : SharingTreeGraph s m G)

/-- The allowance-free sharing label of an existing edge. -/
noncomputable def primitive (h : SharingTreeGraph s m G) (e : G.Edge) : Primitive := by
  classical
  have _ := h.labels e
  exact if G.edgeLabel e = primitiveLabel d (.weakening s) then .weakening s else .contraction s

theorem primitive_label (e : G.Edge) : primitiveLabel d (h.primitive e) = G.edgeLabel e := by
  classical
  unfold primitive
  split
  · rename_i eq; exact eq.symm
  · rename_i ne; exact ((h.labels e).resolve_left ne).symm

theorem primitive_cases (e : G.Edge) : h.primitive e = .weakening s ∨ h.primitive e = .contraction s := by
  classical
  unfold primitive
  split
  · exact .inl rfl
  · exact .inr rfl

/-- Erasing the allowance changes only labels; all carriers and incidences are
literally inherited from the actual graph. -/
@[reducible] noncomputable def tree : ContractionTree s m where
  net := {
    Internal := G.Internal
    Edge := G.Edge
    finiteInternal := G.finiteInternal
    finiteEdge := G.finiteEdge
    internalLabel := G.internalLabel
    edgeLabel := h.primitive
    source := G.source
    target := G.target
    source_nodup := G.source_nodup
    target_nodup := G.target_nodup
    source_unique := G.source_unique
    target_unique := G.target_unique
    source_coverage := G.source_coverage
    target_coverage := G.target_coverage
    source_typed e := by
      rw [G.source_typed, ← h.primitive_label e, primitive_input]
    target_typed e := by
      rw [G.target_typed, ← h.primitive_label e, primitive_output]
  }
  labels := h.primitive_cases
  acyclic {es} path := by
    have mapped : G.Path es := by
      induction path with
      | single e => exact Net.Path.single (G := G) e
      | cons adj path ih => exact Net.Path.cons (G := G) adj ih
    exact h.acyclic mapped

/-- The recovered tree is the original hypernet, up to identity carrier maps;
ordered interfaces, token coordinates and every incidence are preserved. -/
noncomputable def treeIso : DeepIso (h.tree.atDepth d) G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := by
    change LabelEquiv d (primitiveLabel d (h.primitive e)) (G.edgeLabel e)
    rw [h.primitive_label]
    exact labelEquiv_refl d _
  source e := by
    change G.Edge at e
    change (G.source e).map (Port.map id) = G.source e
    exact List.map_id'' (fun v => by cases v <;> rfl) _
  target e := by
    change G.Edge at e
    change (G.target e).map (Port.map id) = G.target e
    exact List.map_id'' (fun v => by cases v <;> rfl) _

end SharingTreeGraph

namespace SharingTreeContext
variable {s : ShareSort} {m d : Nat} (C : SharingTreeContext s m d)

/-- Expansion by sharing-only acyclic fillings produces an actual tree at the
same outer interface, with no assumption of any canonical tree presentation. -/
theorem expandedTree
    (H : (e : C.net.Edge) → Hypernet d ((alphabet d).signature.input (C.net.edgeLabel e))
      ((alphabet d).signature.output (C.net.edgeLabel e)))
    (labels : ∀ e f, (H e).edgeLabel f = primitiveLabel d (.weakening s) ∨
      (H e).edgeLabel f = primitiveLabel d (.contraction s))
    (acyclic : ∀ e {es}, (H e).Path es → es.Nodup) :
    SharingTreeGraph s m (C.net.expand H) where
  labels e := labels e.1 e.2
  acyclic := C.expansion_acyclic H labels acyclic

end SharingTreeContext
end Hypernets.Copying
