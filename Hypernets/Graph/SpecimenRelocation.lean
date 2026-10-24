import Hypernets.Graph.FocusExpansion
import Hypernets.Graph.UAMStructure

/-! Rebuilding an allowed recursive specimen at a synchronized search coordinate. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace FocusExpansion
variable {T : LayeredPreTemplate ops} {C : Hypernet ops d [.term] []} {H K}
    (q : TypedPosition C)

/-- Old retained, filled, and boxed certificates survive focus insertion. -/
theorem edge_lift {e : C.Edge} (cert : DeepFillingEdge T C H K e) :
    DeepFillingEdge T (inserted C q) (family C H q) (family C K q) (.inl e) := by
  cases cert with
  | retained l r =>
      exact .retained ⟨l.edge,l.label,l.source,l.target,l.only⟩
        ⟨r.edge,r.label,r.source,r.target,r.only⟩
  | filled h label rel => exact .filled h label rel
  | boxed b label inner l r => exact .boxed b label inner l r

/-- The new focus is retained on both sides, rather than treated as a hole. -/
theorem edges_lift (cert : ∀ e, DeepFillingEdge T C H K e) :
    ∀ e, DeepFillingEdge T (inserted C q) (family C H q) (family C K q) e := by
  intro e
  cases e with
  | inl e => exact edge_lift q (cert e)
  | inr i =>
      exact .retained ⟨0,rfl,rfl,rfl,fun x => Fin.ext (by omega)⟩
        ⟨0,rfl,rfl,rfl,fun x => Fin.ext (by omega)⟩

/-- Closure follows from the commuting isomorphism and insertion's hole law. -/
theorem closed (H) (closed : HoleFree (C.expand H)) :
    HoleFree ((inserted C q).expand (family C H q)) :=
  (DeepIso.holeFree_iff (DeepIso.ofIso (iso C H q))).mpr
    (FocusInsertion.holeFree _ _ _ _ _ closed)
end FocusExpansion

namespace DeepSpecimen
variable {T : LayeredPreTemplate ops} {Allowed : Hypernet ops d [.term] [] → Prop}
    (S : DeepSpecimen T Allowed)

/-- Relocation retains every original recursive filling and supplies the new
focus as a shared corolla. All context and closure fields are constructed. -/
noncomputable def relocate (closed : IsoClosedContexts Allowed)
    (q : TypedPosition S.focus.underlying) : DeepSpecimen T Allowed where
  context := S.contextAt q
  focus := S.focusAt q
  allowed := S.contextAt_allowed closed q
  left := FocusExpansion.family _ (ExpansionErasure.erasedFamily _ S.left S.focus) q
  right := FocusExpansion.family _ (ExpansionErasure.erasedFamily _ S.right S.focus) q
  edges := FocusExpansion.edges_lift q S.erased_edges
  left_closed := FocusExpansion.closed q _ (ExpansionErasure.expanded_closed _ _ _
    S.focusCopies.1 (fun e ne => (S.other_free e ne).1) S.left_closed)
  right_closed := FocusExpansion.closed q _ (ExpansionErasure.expanded_closed _ _ _
    S.focusCopies.2 (fun e ne => (S.other_free e ne).2) S.right_closed)

/-- The rebuilt left endpoint is exactly the synchronized realization up to names. -/
noncomputable def relocate_left_iso (closed : IsoClosedContexts Allowed)
    (q : TypedPosition S.focus.underlying) :
    Focussed.Iso (S.relocate closed q).leftState.focussed (S.leftAt q).focussed :=
  Focussed.isoOfGraph (FocusExpansion.iso _ _ q)

/-- The same identification holds independently for the right endpoint. -/
noncomputable def relocate_right_iso (closed : IsoClosedContexts Allowed)
    (q : TypedPosition S.focus.underlying) :
    Focussed.Iso (S.relocate closed q).rightState.focussed (S.rightAt q).focussed :=
  Focussed.isoOfGraph (FocusExpansion.iso _ _ q)

/-- The relocated specimen is remote whenever its coordinate is remote. -/
theorem relocate_remote (closed : IsoClosedContexts Allowed)
    (q : TypedPosition S.focus.underlying) (remote : RemotePosition S.focus.underlying q.val) :
    (S.relocate closed q).focus.mode ≠ .rewrite ∨ ¬ (S.relocate closed q).focus.Entering :=
  S.focusAt_remote q remote

/-- Lemma 39(3)'s successor is an actual allowed specimen, not just a pair of
coordinates. Both endpoint transitions and remote status are proved. -/
theorem settled_successor (allowed : IsoClosedContexts Allowed)
    (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    (settled : S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering))
    (enabled : (∃ t, State.DeepSearch kind S.leftState t) ∨
      (∃ t, State.DeepSearch kind S.rightState t)) :
    ∃ D : DeepSpecimen T Allowed,
      (D.focus.mode ≠ .rewrite ∨ ¬ D.focus.Entering) ∧
      State.DeepSearch kind S.leftState D.leftState ∧ State.DeepSearch kind S.rightState D.rightState := by
  obtain ⟨q,_,remote,ls,rs,_,_⟩ := S.settled_traversal closed left right settled enabled
  refine ⟨S.relocate allowed q,S.relocate_remote allowed q remote,?_,?_⟩
  · exact (State.deepSearch_iso_iff (Focussed.DeepIso.refl S.leftState.focussed)
      (Focussed.DeepIso.ofIso (S.relocate_left_iso allowed q).symm)).mp ls
  · exact (State.deepSearch_iso_iff (Focussed.DeepIso.refl S.rightState.focussed)
      (Focussed.DeepIso.ofIso (S.relocate_right_iso allowed q).symm)).mp rs

/-- In settled modes a full UAM step must be search; no behaviour locality is assumed. -/
theorem settled_step_search {kind : Op → OperationKind} (B : Behaviour ops d kind)
    (settled : S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering))
    {t : State ops d} (step : UAM.Step B S.leftState t) : State.Search kind S.leftState t := by
  rcases (UAM.step_iff B).mp step with search | rewrite
  · exact search
  · have mode : S.focus.mode = .rewrite := (UAM.rewrite_modes B rewrite).1
    rcases settled with back | ⟨search,_⟩
    · cases back.symm.trans mode
    · cases search.symm.trans mode

/-- Full-UAM context traversal produces an actual successor specimen. Since
settled sources cannot rewrite, the conclusion consists of literal search steps. -/
theorem full_context_step {kind : Op → OperationKind} (B : Behaviour ops d kind)
    (allowed : IsoClosedContexts Allowed) (closed : (T d).OutputClosed)
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    (settled : S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering))
    (enabled : (∃ t, UAM.Step B S.leftState t) ∨ (∃ t, UAM.Step B S.rightState t)) :
    ∃ D : DeepSpecimen T Allowed,
      (D.focus.mode ≠ .rewrite ∨ ¬ D.focus.Entering) ∧
      UAM.Step B S.leftState D.leftState ∧ UAM.Step B S.rightState D.rightState := by
  have away := S.settled_away closed left right settled
  have extract : ∃ q : TypedPosition S.focus.underlying,
      SearchStep S.focus.underlying kind S.focus.coordinate.val q.val := by
    rcases enabled with ⟨t,step⟩ | ⟨t,step⟩
    · obtain ⟨q,h,_⟩ := (S.left_search_iff away kind t).mp (S.settled_step_search B settled step)
      exact ⟨q,h⟩
    · have search : State.Search kind S.rightState t := by
        rcases (UAM.step_iff B).mp step with search | rewrite
        · exact search
        · have mode : S.focus.mode = .rewrite := (UAM.rewrite_modes B rewrite).1
          rcases settled with back | ⟨search,_⟩
          · cases back.symm.trans mode
          · cases search.symm.trans mode
      obtain ⟨q,h,_⟩ := (S.right_search_iff away kind t).mp search
      exact ⟨q,h⟩
  obtain ⟨q,h⟩ := extract
  exact ⟨S.relocate allowed q,S.relocate_remote allowed q h.remote_target,
    .inl (.inl ((S.left_search_iff away kind _).mpr
      ⟨q,h,⟨(S.relocate_left_iso allowed q).symm⟩⟩)),
    .inl (.inl ((S.right_search_iff away kind _).mpr
      ⟨q,h,⟨(S.relocate_right_iso allowed q).symm⟩⟩))⟩


/-- Relocation to the unique input yields two initial states, even if the
original specimen was unrooted. -/
theorem relocate_initial (allowed : IsoClosedContexts Allowed) :
    (S.relocate allowed (TypedPosition.initial S.focus.underlying)).leftState.focussed.Initial ∧
    (S.relocate allowed (TypedPosition.initial S.focus.underlying)).rightState.focussed.Initial := by
  let D := S.relocate allowed (TypedPosition.initial S.focus.underlying)
  have initial : D.focus.Initial := ⟨rfl,trivial⟩
  have left := (ExpansionPaths.focussed_boundary _ _ D.focus D.focusCopies.1
    (fun e ne => (D.other_free e ne).1)).1.mpr initial
  exact ⟨left,D.boundary_agreement.1.mp left⟩

include S in
/-- The constructed initial specimen belongs to the concrete remote rooted lifting. -/
theorem initial_witness (allowed : IsoClosedContexts Allowed) (kind : Op → OperationKind) :
    ∃ D : DeepSpecimen T Allowed, D.focus.mode = .search ∧
      D.leftState.focussed.Initial ∧ D.rightState.focussed.Initial ∧
      State.Rooted kind D.leftState ∧ State.Rooted kind D.rightState := by
  obtain ⟨left,right⟩ := S.relocate_initial allowed
  exact ⟨S.relocate allowed (TypedPosition.initial S.focus.underlying),rfl,left,right,
    DeepStateClass.initial_rooted left,DeepStateClass.initial_rooted right⟩

end DeepSpecimen
end Hypernets.Linear
