import Hypernets.Graph.LocalInteraction

/-! Independent incidence equations for contextual movement of the focus. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace Focussed
variable {C : Hypernet ops d [.term] []} (f : Focussed C)

/-- Join the two ends of the old focus, expressed on original graph ports. -/
noncomputable def joinPort (v : C.Vertex) : C.Vertex := by
  classical
  exact if v = f.target then f.source else v

/-- Redirect the selected joined port to the reusable internal focus target. -/
noncomputable def movePort (selected v : C.Vertex) : C.Vertex := by
  classical
  exact if f.joinPort v = f.joinPort selected then f.target else f.joinPort v

theorem joinPort_eq_lift_contract (v : C.Vertex) :
    f.joinPort v = FocusErasure.lift f.targetVertex
      (FocusErasure.contract f f.targetVertex f.targetVertex_spec v) := by
  classical
  by_cases eq : v = f.target
  · subst v
    rw [f.targetVertex_spec,FocusErasure.contract_target,FocusErasure.lift_position]
    simp [joinPort, ← f.targetVertex_spec]
  · have ne : v ≠ .internal f.targetVertex := fun h => eq (h.trans f.targetVertex_spec.symm)
    rw [FocusErasure.lift_contract f f.targetVertex f.targetVertex_spec v ne]
    simp [joinPort,eq]

/-- Outside the old target and the selected joined port, source incidences do not change. -/
theorem movePort_unchanged {selected v : C.Vertex}
    (old : v ≠ f.target) (new : v ≠ f.joinPort selected) : f.movePort selected v = v := by
  classical
  have j : f.joinPort v = v := by simp [joinPort,old]
  simp only [movePort,j,ite_eq_right new]

end Focussed

/-- A contextual local rewiring, specified without erasure or SearchStep.
All carriers, boundary ports, types, non-focus labels, and target incidences are
retained up to explicit names. Only the focus label/source and the two affected
source connections change. -/
structure LocalRewiring (s t : State ops d) (p : Focus × s.graph.Vertex) where
  vertices : Bijection s.graph.Internal t.graph.Internal
  edges : Bijection s.graph.Edge t.graph.Edge
  internal_label : ∀ v, t.graph.internalLabel (vertices.toFun v) = s.graph.internalLabel v
  focus : edges.toFun s.focussed.edge = t.focussed.edge
  mode : t.focussed.mode = p.1
  label_other : ∀ e, e ≠ s.focussed.edge →
    t.graph.edgeLabel (edges.toFun e) = s.graph.edgeLabel e
  source_focus : t.graph.source (edges.toFun s.focussed.edge) =
    [Port.map vertices.toFun (s.focussed.joinPort p.2)]
  source_other : ∀ e, e ≠ s.focussed.edge →
    t.graph.source (edges.toFun e) = (s.graph.source e).map
      (fun v => Port.map vertices.toFun (s.focussed.movePort p.2 v))
  target : ∀ e, t.graph.target (edges.toFun e) =
    (s.graph.target e).map (Port.map vertices.toFun)

namespace LocalRewiring

private theorem port_trans {A B C : Type} {n m : Nat} (a : Bijection A B) (b : Bijection B C) :
    Port.map (a.trans b).toFun (n := n) (m := m) =
      fun v => Port.map b.toFun (Port.map a.toFun v) := by
  funext v
  cases v <;> rfl
variable (s : State ops d) (p : Focus × s.graph.Vertex)
    (q : TypedPosition s.focussed.underlying)



/-- Restoring carrier names after inserting at q implements the explicit source rewiring. -/
theorem restore_move (compatible : q.val = p.map id (FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec)) (v : s.graph.Vertex) :
    Port.map (FocusErasure.restore s.focussed.targetVertex).toFun
      (FocusInsertion.split s.focussed.underlying q.val.2
        (FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec v)) =
      s.focussed.movePort p.2 v := by
  classical
  have coord := congrArg Prod.snd compatible
  change q.val.2 = FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec p.2 at coord
  rw [coord]
  have iffEq : FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec v =
      FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec p.2 ↔
      s.focussed.joinPort v = s.focussed.joinPort p.2 := by
    rw [s.focussed.joinPort_eq_lift_contract v,s.focussed.joinPort_eq_lift_contract p.2]
    exact ⟨congrArg _,FocusErasure.lift_injective _⟩
  by_cases eq : s.focussed.joinPort v = s.focussed.joinPort p.2
  · rw [FocusInsertion.split,ite_eq_left (iffEq.mpr eq)]
    change Port.internal s.focussed.targetVertex = _
    simp [Focussed.movePort,eq,s.focussed.targetVertex_spec]
  · rw [FocusInsertion.split,ite_eq_right (fun h => eq (iffEq.mp h))]
    rw [FocusErasure.restore_host s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec]
    rw [← s.focussed.joinPort_eq_lift_contract]
    simp [Focussed.movePort,eq]

/-- Any target satisfying the local incidence equations is isomorphic to the
independently constructed erased-coordinate successor. -/
noncomputable def iso (compatible : q.val = p.map id (FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec)) {t : State ops d} (rewire : LocalRewiring s t p) :
    Focussed.Iso (q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)).focussed t.focussed where
  graph := {
    vertices := (FocusErasure.restore s.focussed.targetVertex).trans rewire.vertices
    edges := (FocusErasure.restore s.focussed.edge).trans rewire.edges
    internal_label := by
      intro v
      cases v with
      | inl v => exact rewire.internal_label v.val
      | inr i =>
          exact (rewire.internal_label s.focussed.targetVertex).trans
            (FocusErasure.target_term s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec)
    edge_label := by
      intro e
      cases e with
      | inl e => exact rewire.label_other e.val e.property
      | inr i =>
          change t.graph.edgeLabel (rewire.edges.toFun s.focussed.edge) = focusLabel ops d q.val.1
          rw [rewire.focus,t.focussed.label,rewire.mode]
          exact congrArg (focusLabel ops d) (congrArg Prod.fst compatible).symm
    source := by
      intro e
      cases e with
      | inl e =>
          change (((s.graph.source e.val).map (FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec)).map (FocusInsertion.split s.focussed.underlying q.val.2)).map
            (Port.map ((FocusErasure.restore s.focussed.targetVertex).trans rewire.vertices).toFun) = t.graph.source (rewire.edges.toFun e.val)
          rw [port_trans,rewire.source_other e.val e.property]
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          exact congrArg (Port.map rewire.vertices.toFun) (restore_move s p q compatible v)
      | inr i =>
          change [Port.map ((FocusErasure.restore s.focussed.targetVertex).trans rewire.vertices).toFun (FocusInsertion.host s.focussed.underlying q.val.2)] =
            t.graph.source (rewire.edges.toFun s.focussed.edge)
          rw [port_trans,rewire.source_focus]
          apply congrArg (fun v => [Port.map rewire.vertices.toFun v])
          exact (FocusErasure.restore_host s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec q.val.2).trans
            ((congrArg (FocusErasure.lift s.focussed.targetVertex) (congrArg Prod.snd compatible)).trans
              (s.focussed.joinPort_eq_lift_contract p.2).symm)
    target := by
      intro e
      cases e with
      | inl e =>
          change (((s.graph.target e.val).map (FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec)).map (FocusInsertion.host s.focussed.underlying)).map
            (Port.map ((FocusErasure.restore s.focussed.targetVertex).trans rewire.vertices).toFun) = t.graph.target (rewire.edges.toFun e.val)
          rw [port_trans,rewire.target]
          simp only [List.map_map]
          apply List.map_congr_left
          intro v mem
          apply congrArg (Port.map rewire.vertices.toFun)
          exact (FocusErasure.restore_host s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec _).trans
            (FocusErasure.lift_contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec v
              (FocusErasure.target_avoids s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec e.property mem))
      | inr i =>
          change [Port.map rewire.vertices.toFun (.internal s.focussed.targetVertex)] =
            t.graph.target (rewire.edges.toFun s.focussed.edge)
          rw [rewire.target,s.focussed.target_eq,s.focussed.targetVertex_spec]
          rfl }
  mode := (congrArg Prod.fst compatible).trans rewire.mode.symm
  focus := rewire.focus

/-- The canonical erased-coordinate successor satisfies the independent local equations. -/
noncomputable def canonical
    (compatible : q.val = p.map id (FocusErasure.contract s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec)) :
    LocalRewiring s (q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)) p where
  vertices := (FocusErasure.restore s.focussed.targetVertex).symm
  edges := (FocusErasure.restore s.focussed.edge).symm
  internal_label := by
    intro v
    have h := (FocusErasure.reinsert_iso s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec).symm.internal_label v
    exact h
  focus := by
    classical
    simp [FocusErasure.restore,Bijection.symm,TypedPosition.realize,FocusInsertion.focussed]
  mode := congrArg Prod.fst compatible
  label_other := by
    intro e ne
    change (FocusInsertion.insert s.focussed.underlying q.val.2 q.property q.not_output q.val.1).edgeLabel _ = _
    simp [FocusErasure.restore,Bijection.symm,ne]
  source_focus := by
    classical
    change (FocusInsertion.insert s.focussed.underlying q.val.2 q.property q.not_output q.val.1).source _ = _
    simp only [Bijection.symm,FocusErasure.restore,dite_true,FocusInsertion.insert]
    apply congrArg List.singleton
    apply (Port.bijection (FocusErasure.restore s.focussed.targetVertex)).injective
    change Port.map (FocusErasure.restore s.focussed.targetVertex).toFun
      (FocusInsertion.host s.focussed.underlying q.val.2) = _
    apply Eq.trans ?_ ((Port.bijection (FocusErasure.restore s.focussed.targetVertex)).right_inv _).symm
    exact (FocusErasure.restore_host s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec _).trans
      ((congrArg (FocusErasure.lift s.focussed.targetVertex) (congrArg Prod.snd compatible)).trans
        (s.focussed.joinPort_eq_lift_contract p.2).symm)
  source_other := by
    classical
    intro e ne
    change (FocusInsertion.insert s.focussed.underlying q.val.2 q.property q.not_output q.val.1).source _ = _
    simp only [Bijection.symm,FocusErasure.restore,dite_eq_right ne]
    change (((s.graph.source e).map _).map _) = _
    rw [List.map_map]
    apply List.map_congr_left
    intro v _
    apply (Port.bijection (FocusErasure.restore s.focussed.targetVertex)).injective
    exact (restore_move s p q compatible v).trans
      ((Port.bijection (FocusErasure.restore s.focussed.targetVertex)).right_inv _).symm
  target := by
    intro e
    exact (FocusErasure.reinsert_iso s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec).symm.target e |>.symm

/-- Rewiring is unchanged by a focus-preserving renaming of its target. -/
def transport {s t u : State ops d} {p} (r : LocalRewiring s t p)
    (a : Focussed.Iso t.focussed u.focussed) : LocalRewiring s u p where
  vertices := r.vertices.trans a.graph.vertices
  edges := r.edges.trans a.graph.edges
  internal_label v := (a.graph.internal_label _).trans (r.internal_label v)
  focus := by change a.graph.edges.toFun (r.edges.toFun s.focussed.edge) = _; rw [r.focus,a.focus]
  mode := a.mode.symm.trans r.mode
  label_other e ne := (a.graph.edge_label _).trans (r.label_other e ne)
  source_focus := by
    change u.graph.source (a.graph.edges.toFun (r.edges.toFun s.focussed.edge)) = _
    rw [← a.graph.source,r.source_focus,port_trans]
    rfl
  source_other := by
    intro e ne
    change u.graph.source (a.graph.edges.toFun (r.edges.toFun e)) = _
    rw [← a.graph.source,r.source_other e ne,port_trans,List.map_map]
    rfl
  target := by
    intro e
    change u.graph.target (a.graph.edges.toFun (r.edges.toFun e)) = _
    rw [← a.graph.target,r.target,port_trans,List.map_map]
    rfl

end LocalRewiring

namespace State
/-- Search specified by an original-graph interaction and independent local incidence equations. -/
def IncidenceSearch (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  ∃ p, LocalInteraction s.focussed kind p ∧ Nonempty (LocalRewiring s t p)

/-- Erasure-based search is exactly the independent incidence presentation. -/
theorem search_iff_incidence {kind : Op → OperationKind} {s t : State ops d} :
    Search kind s t ↔ IncidenceSearch kind s t := by
  constructor
  · rintro ⟨q,step,⟨a⟩⟩
    obtain ⟨p,interaction,compatible⟩ := LocalInteraction.complete step
    exact ⟨p,interaction,⟨(LocalRewiring.canonical s p q compatible).transport a⟩⟩
  · rintro ⟨p,interaction,⟨rewire⟩⟩
    have step := interaction.sound
    let q : TypedPosition s.focussed.underlying := ⟨_,step.preserves_term s.focussed.coordinate.property⟩
    exact ⟨q,step,⟨LocalRewiring.iso s p q rfl rewire⟩⟩
/-- Recursive endpoint renaming introduces no additional incidence interactions. -/
theorem deepSearch_iff_incidence {kind : Op → OperationKind} {s t : State ops d} :
    DeepSearch kind s t ↔
      ∃ u, IncidenceSearch kind s u ∧ Nonempty (Focussed.DeepIso u.focussed t.focussed) := by
  rw [deepSearch_iff]
  simp only [search_iff_incidence]

/-- The independent local equations determine the successor up to names. -/
theorem incidenceSearch_deterministic {kind : Op → OperationKind} {s t u : State ops d}
    (left : IncidenceSearch kind s t) (right : IncidenceSearch kind s u) :
    Nonempty (Focussed.Iso t.focussed u.focussed) :=
  search_deterministic (search_iff_incidence.mpr left) (search_iff_incidence.mpr right)
end State
end Hypernets.Linear
