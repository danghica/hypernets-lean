import Hypernets.Graph.FocusErasure

/-! Reinsertion after general erasure recovers the original focussed graph
up to an explicit literal-label isomorphism, preserving its focus endpoints. -/
namespace Hypernets.Linear.FocusErasure
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}
    {G : Hypernet ops d I []} (f : Focussed G) (t : G.Internal)
    (target_eq : f.target = .internal t)

/-- Restore one deleted element with a fresh singleton carrier. -/
noncomputable def restore {A : Type} (a : A) : Bijection ({x : A // x ≠ a} ⊕ Fin 1) A := by
  classical
  exact {
    toFun := fun x => match x with | .inl x => x.val | .inr _ => a
    invFun := fun x => if h : x = a then .inr 0 else .inl ⟨x, h⟩
    left_inv := by
      intro x
      cases x with
      | inl x => simp [x.property]
      | inr i => have eq : i = 0 := Fin.ext (by omega); subst i; simp
    right_inv := by intro x; by_cases h : x = a <;> simp [h]
  }

theorem position_not_output : ¬ (position f t target_eq).IsOutput := by
  cases position f t target_eq with
  | internal _ => exact id
  | input _ => exact id
  | output i => exact Fin.elim0 i

/-- Reinsert the original mode at the joined vertex of the erased graph. -/
noncomputable def reinsert : Hypernet ops d I [] :=
  FocusInsertion.insert (erase f t target_eq) (position f t target_eq)
    (position_term f t target_eq) (position_not_output f t target_eq) f.mode

theorem restore_host (x : Vertex (G := G) t) :
    Port.map (restore t).toFun (FocusInsertion.host (erase f t target_eq) x) = lift t x := by
  cases x <;> rfl

theorem restore_fresh :
    Port.map (restore t).toFun (FocusInsertion.fresh (erase f t target_eq)) = .internal t := rfl

theorem restore_split (x : Vertex (G := G) t) :
    Port.map (restore t).toFun
      (FocusInsertion.split (erase f t target_eq) (position f t target_eq) x) = expand f t x := by
  classical
  by_cases eq : x = position f t target_eq
  · subst x
    simp [FocusInsertion.split, restore_fresh, expand, lift_position]
  · have ne : lift t x ≠ f.source := by
      intro h
      apply eq
      apply lift_injective t
      exact h.trans (lift_position f t target_eq).symm
    simp [FocusInsertion.split, eq, restore_host, expand, ne]

/-- The original names are restored for every vertex and edge; boundary order
and complete labels, including all box bodies, are preserved. -/
noncomputable def reinsert_iso : Net.Iso (reinsert f t target_eq) G where
  vertices := restore t
  edges := restore f.edge
  internal_label := by
    intro x
    cases x with
    | inl x => rfl
    | inr i => exact target_term f t target_eq
  edge_label := by
    intro e
    cases e with
    | inl e => rfl
    | inr i => exact f.label
  source := by
    intro e
    cases e with
    | inl e =>
        change (((G.source e.val).map (contract f t target_eq)).map
          (FocusInsertion.split (erase f t target_eq) (position f t target_eq))).map
          (Port.map (restore t).toFun) = G.source e.val
        simp only [List.map_map]
        have point : ∀ w ∈ G.source e.val,
            Port.map (restore t).toFun (FocusInsertion.split (erase f t target_eq)
              (position f t target_eq) (contract f t target_eq w)) = w := by
          intro w hw
          rw [restore_split, expand_contract f t target_eq w (source_avoids f e.property hw)]
        simpa only [List.map_id, Function.comp_def] using (List.map_congr_left (f := _) (g := id) point)
    | inr i =>
        change [Port.map (restore t).toFun (FocusInsertion.host (erase f t target_eq) (position f t target_eq))] = G.source f.edge
        rw [restore_host, lift_position, f.source_eq]
  target := by
    intro e
    cases e with
    | inl e =>
        change (((G.target e.val).map (contract f t target_eq)).map
          (FocusInsertion.host (erase f t target_eq))).map (Port.map (restore t).toFun) = G.target e.val
        simp only [List.map_map]
        have point : ∀ w ∈ G.target e.val,
            Port.map (restore t).toFun (FocusInsertion.host (erase f t target_eq)
              (contract f t target_eq w)) = w := by
          intro w hw
          rw [restore_host, lift_contract f t target_eq w (target_avoids f t target_eq e.property hw)]
        simpa only [List.map_id, Function.comp_def] using (List.map_congr_left (f := _) (g := id) point)
    | inr i =>
        change [Port.map (restore t).toFun (FocusInsertion.fresh (erase f t target_eq))] = G.target f.edge
        rw [restore_fresh, f.target_eq, target_eq]

/-- The round-trip isomorphism sends the new focus edge to the original one. -/
theorem reinsert_focus_edge : (reinsert_iso f t target_eq).edges.toFun (.inr 0) = f.edge := rfl

/-- The round trip preserves the actual source and target of the focus. -/
theorem reinsert_focus_endpoints :
    Port.map (reinsert_iso f t target_eq).vertices.toFun
      (FocusInsertion.host (erase f t target_eq) (position f t target_eq)) = f.source ∧
    Port.map (reinsert_iso f t target_eq).vertices.toFun
      (FocusInsertion.fresh (erase f t target_eq)) = f.target :=
  ⟨(restore_host f t target_eq _).trans (lift_position f t target_eq),
    (restore_fresh f t target_eq).trans target_eq.symm⟩

end Hypernets.Linear.FocusErasure

namespace Hypernets.Linear.Focussed
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}
    {G : Hypernet ops d I []} (f : Focussed G)

/-- In a graph without outputs, a focus target must be internal: it cannot
be an input because it occurs in the focus's target list. -/
theorem target_internal : ∃ t : G.Internal, f.target = .internal t := by
  have mem : f.target ∈ G.target f.edge := by rw [f.target_eq]; simp
  have no := G.target_not_input mem
  cases eq : f.target with
  | internal t => exact ⟨t, rfl⟩
  | input i => rw [eq] at no; exact False.elim (no trivial)
  | output i => exact Fin.elim0 i

noncomputable def targetVertex : G.Internal := Classical.choose f.target_internal

theorem targetVertex_spec : f.target = .internal f.targetVertex := Classical.choose_spec f.target_internal

/-- Erasure for every focussed graph with a closed output interface. -/
noncomputable def underlying : Hypernet ops d I [] :=
  FocusErasure.erase f f.targetVertex f.targetVertex_spec

theorem underlying_focusFree : FocusFree f.underlying :=
  FocusErasure.erased_focusFree f f.targetVertex f.targetVertex_spec

theorem underlying_holeFree (free : HoleFree G) : HoleFree f.underlying :=
  FocusErasure.erased_holeFree f f.targetVertex f.targetVertex_spec free

/-- Every such focussed graph is obtained, up to isomorphism, by inserting its
mode into its focus-free underlying graph. This is not restricted to prior insertions. -/
noncomputable def underlying_reinsert_iso :
    Net.Iso (FocusErasure.reinsert f f.targetVertex f.targetVertex_spec) G :=
  FocusErasure.reinsert_iso f f.targetVertex f.targetVertex_spec

end Hypernets.Linear.Focussed
