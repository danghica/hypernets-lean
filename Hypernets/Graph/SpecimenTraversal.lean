import Hypernets.Graph.ExpansionErasure

/-! Actual-state traversal of recursive specimens via the erasure bridge. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- Removing a retained focus leaves the recursive certificates at all other edges. -/
theorem DeepFillingEdge.erased {T : LayeredPreTemplate ops} {C : Hypernet ops d [.term] []}
    {H K} (f : Focussed C) (e : f.underlying.Edge) (cert : DeepFillingEdge T C H K e.val) :
    DeepFillingEdge T f.underlying (ExpansionErasure.erasedFamily C H f)
      (ExpansionErasure.erasedFamily C K f) e := by
  cases cert with
  | retained l r =>
      exact .retained ⟨l.edge,l.label,l.source,l.target,l.only⟩ ⟨r.edge,r.label,r.source,r.target,r.only⟩
  | filled h label rel => exact .filled h label rel
  | boxed b label inner l r => exact .boxed b label inner l r

namespace ExpansionErasure
variable {C : Hypernet ops d [.term] []}
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (f : Focussed C) (copy : ExpansionPaths.CorollaCopy C H f.edge)
    (free : ∀ e, e ≠ f.edge → FocusFree (H e)) (closed : HoleFree (C.expand H))

/-- Every typed erased-context coordinate defines a state in the same filling. -/
noncomputable def stateAt (q : TypedPosition f.underlying) : State ops d :=
  (q.expand (erasedFamily C H f)).realize (expanded_free C H f copy free)
    (expanded_closed C H f copy free closed)

/-- Exact characterization of actual state successors away from a shallow hole
boundary, allowing arbitrary target carriers up to focus-preserving isomorphism. -/
theorem search_iff
    (preserves : ExpansionSearch.PreservesSearch f.underlying (erasedFamily C H f))
    (origins : ExpansionSearch.SearchOrigins f.underlying (erasedFamily C H f))
    (away : ¬ ExpansionSearch.HoleBoundary f.underlying f.coordinate.val)
    (kind : Op → OperationKind) (target : State ops d) :
    State.Search kind (ExpansionPaths.state H f copy free closed) target ↔
      ∃ q : TypedPosition f.underlying,
        SearchStep f.underlying kind f.coordinate.val q.val ∧
        Nonempty (Focussed.Iso (stateAt H f copy free closed q).focussed target.focussed) := by
  have bridge := realization_iso C H f copy free closed
  rw [← State.search_iso_iff bridge (Focussed.Iso.refl target.focussed)]
  rw [TypedPosition.search_realize_iff]
  constructor
  · rintro ⟨r,step,iso⟩
    obtain ⟨q,original,eq⟩ := (ExpansionSearch.step_iff f.underlying (erasedFamily C H f)
      preserves origins f.coordinate.val away).mp step
    let typed : TypedPosition f.underlying := ⟨q,original.preserves_term f.coordinate.property⟩
    have same : r = typed.expand (erasedFamily C H f) := Subtype.ext eq
    rw [same] at iso
    exact ⟨typed,original,iso⟩
  · rintro ⟨q,step,iso⟩
    exact ⟨q.expand (erasedFamily C H f),
      ExpansionSearch.step f.underlying (erasedFamily C H f) preserves step,iso⟩

/-- Context runs start at the original expanded state, not merely an isomorphic
state introduced by a separate realization construction. -/
theorem steps (preserves : ExpansionSearch.PreservesSearch f.underlying (erasedFamily C H f))
    {kind : Op → OperationKind} {n} (q : TypedPosition f.underlying)
    (run : (coordinateMachine f.underlying kind).Steps n f.coordinate.val q.val) :
    (DeepStateClass.searchMachine kind).Steps n
      (DeepStateClass.ofState (ExpansionPaths.state H f copy free closed))
      (DeepStateClass.ofState (stateAt H f copy free closed q)) := by
  have trace := (f.coordinate.expand (erasedFamily C H f)).realize_steps
    (expanded_free C H f copy free) (expanded_closed C H f copy free closed)
    (q.expand (erasedFamily C H f))
    (ExpansionSearch.steps f.underlying (erasedFamily C H f) preserves run)
  have eq : DeepStateClass.ofState (stateAt H f copy free closed f.coordinate) =
      DeepStateClass.ofState (ExpansionPaths.state H f copy free closed) :=
    Quotient.sound ⟨Focussed.DeepIso.ofIso (realization_iso C H f copy free closed)⟩
  exact eq ▸ trace

/-- A context-only initial run proves rootedness of the original expanded state. -/
theorem rooted (preserves : ExpansionSearch.PreservesSearch f.underlying (erasedFamily C H f))
    {kind : Op → OperationKind} {n}
    (run : (coordinateMachine f.underlying kind).Steps n
      (TypedPosition.initial f.underlying).val f.coordinate.val) :
    State.Rooted kind (ExpansionPaths.state H f copy free closed) := by
  have root := (f.coordinate.expand (erasedFamily C H f)).realize_rooted
    (expanded_free C H f copy free) (expanded_closed C H f copy free closed)
    (ExpansionSearch.steps f.underlying (erasedFamily C H f) preserves run)
  have eq : DeepStateClass.ofState (stateAt H f copy free closed f.coordinate) =
      DeepStateClass.ofState (ExpansionPaths.state H f copy free closed) :=
    Quotient.sound ⟨Focussed.DeepIso.ofIso (realization_iso C H f copy free closed)⟩
  change DeepStateClass.Rooted kind (DeepStateClass.ofState (ExpansionPaths.state H f copy free closed))
  rw [← eq]
  exact root

end ExpansionErasure
namespace Focussed
variable {C : Hypernet ops d [.term] []} (f : Focussed C)

/-- A focus enters a shallow hole when its target is a source of that hole. -/
def Entering : Prop := ∃ e h, C.edgeLabel e = primitiveLabel ops d (.hole h) ∧ f.target ∈ C.source e

/-- A focus exits a shallow hole when its source is a target of that hole. -/
def Exiting : Prop := ∃ e h, C.edgeLabel e = primitiveLabel ops d (.hole h) ∧ f.source ∈ C.target e

theorem erased_source_iff (e : f.underlying.Edge) :
    f.coordinate.val.2 ∈ f.underlying.source e ↔ f.target ∈ C.source e.val := by
  classical
  constructor
  · intro mem
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have same := congrArg (FocusErasure.expand f f.targetVertex) eq
    rw [FocusErasure.expand_contract f f.targetVertex f.targetVertex_spec v
      (FocusErasure.source_avoids f e.property hv)] at same
    have joined : FocusErasure.expand f f.targetVertex f.coordinate.val.2 = f.target := by
      change (if FocusErasure.lift f.targetVertex (FocusErasure.position f f.targetVertex f.targetVertex_spec) = f.source
        then (Port.internal f.targetVertex : C.Vertex) else _) = _
      rw [FocusErasure.lift_position, ite_eq_left rfl, ← f.targetVertex_spec]
    rw [joined] at same
    exact same ▸ hv
  · intro mem
    apply List.mem_map.mpr
    refine ⟨f.target,mem,?_⟩
    change FocusErasure.contract f f.targetVertex f.targetVertex_spec f.target = _
    rw [f.targetVertex_spec,FocusErasure.contract_target]
    rfl

theorem erased_target_iff (e : f.underlying.Edge) :
    f.coordinate.val.2 ∈ f.underlying.target e ↔ f.source ∈ C.target e.val := by
  constructor
  · intro mem
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have same := congrArg (FocusErasure.lift f.targetVertex) eq
    rw [FocusErasure.lift_contract f f.targetVertex f.targetVertex_spec v
      (FocusErasure.target_avoids f f.targetVertex f.targetVertex_spec e.property hv)] at same
    exact (same.trans (FocusErasure.lift_position f f.targetVertex f.targetVertex_spec)) ▸ hv
  · intro mem
    exact List.mem_map.mpr ⟨f.source,mem,FocusErasure.contract_source f f.targetVertex f.targetVertex_spec⟩

/-- The erased-coordinate boundary predicate is exactly the mode-sensitive
entering/exiting classification of the original focussed context. -/
theorem boundary_iff : ExpansionSearch.HoleBoundary f.underlying f.coordinate.val ↔
    (f.mode = .search ∧ f.Entering) ∨ (f.mode = .backtrack ∧ f.Exiting) := by
  constructor
  · rintro ⟨e,h,label,case⟩
    rcases case with ⟨mode,mem⟩ | ⟨mode,mem⟩
    · exact .inl ⟨mode,e.val,h,label,(f.erased_source_iff e).mp mem⟩
    · exact .inr ⟨mode,e.val,h,label,(f.erased_target_iff e).mp mem⟩
  · intro cases
    rcases cases with ⟨mode,e,h,label,mem⟩ | ⟨mode,e,h,label,mem⟩
    · have ne : e ≠ f.edge := by
        intro eq; subst e
        exact focusLabel_ne_hole f.mode h (f.label.symm.trans label)
      exact ⟨⟨e,ne⟩,h,label,.inl ⟨mode,(f.erased_source_iff ⟨e,ne⟩).mpr mem⟩⟩
    · have ne : e ≠ f.edge := by
        intro eq; subst e
        exact focusLabel_ne_hole f.mode h (f.label.symm.trans label)
      exact ⟨⟨e,ne⟩,h,label,.inr ⟨mode,(f.erased_target_iff ⟨e,ne⟩).mpr mem⟩⟩

end Focussed

/-- A coordinate is remote when it is not a rewrite focus at a hole source. -/
def RemotePosition {I O} (C : Hypernet ops d I O) (p : SearchPosition C) : Prop :=
  p.1 ≠ .rewrite ∨ ∀ e h, C.edgeLabel e = primitiveLabel ops d (.hole h) → p.2 ∉ C.source e

/-- Search can produce rewrite mode only at an original variable or operation
source, which cannot simultaneously be a hole source by incidence uniqueness. -/
theorem SearchStep.remote_target {I O} {C : Hypernet ops d I O} {kind : Op → OperationKind}
    {p q} (step : SearchStep C kind p q) : RemotePosition C q := by
  have avoid (e : C.Edge) (primitive : Primitive Op)
      (label : C.edgeLabel e = primitiveLabel ops d primitive)
      (nonhole : ∀ h, primitive ≠ .hole h) {v : C.Vertex} (source : v ∈ C.source e) :
      ∀ x h, C.edgeLabel x = primitiveLabel ops d (.hole h) → v ∉ C.source x := by
    intro x h hole mem
    have eq := C.source_unique source mem
    exact nonhole h (primitiveLabel_injective d (label.symm.trans ((congrArg C.edgeLabel eq).trans hole)))
  have operation (a : SearchOperation C) :
      ∀ x h, C.edgeLabel x = primitiveLabel ops d (.hole h) → a.source ∉ C.source x :=
    avoid a.edge (.operation a.operation) a.label (fun _ eq => by cases eq)
      (by rw [a.source_eq]; simp)
  cases step with
  | trigger e v label source =>
      exact .inr (avoid e .variable label (fun _ eq => by cases eq) (by rw [source]; simp))
  | enter a =>
      simp only [SearchOperation.enter]
      split
      next empty => exact .inr (operation a)
      next v rest args => exact .inl (fun eq => by cases eq)
  | resume a i v arg =>
      simp only [SearchOperation.resume]
      split
      next w nextArg => exact .inl (fun eq => by cases eq)
      next none => exact .inr (operation a)

namespace DeepSpecimen
variable {T : LayeredPreTemplate ops} {Allowed : Hypernet ops d [.term] [] → Prop}
    (S : DeepSpecimen T Allowed)

/-- The original paired certificates restrict to the erased context. -/
theorem erased_edges (e : S.focus.underlying.Edge) :
    DeepFillingEdge T S.focus.underlying
      (ExpansionErasure.erasedFamily S.context.val S.left S.focus)
      (ExpansionErasure.erasedFamily S.context.val S.right S.focus) e :=
  (S.edges e.val).erased S.focus e

noncomputable def leftAt (q : TypedPosition S.focus.underlying) : State ops d :=
  ExpansionErasure.stateAt S.left S.focus S.focusCopies.1
    (fun e ne => (S.other_free e ne).1) S.left_closed q

noncomputable def rightAt (q : TypedPosition S.focus.underlying) : State ops d :=
  ExpansionErasure.stateAt S.right S.focus S.focusCopies.2
    (fun e ne => (S.other_free e ne).2) S.right_closed q

/-- The old specimen states and the coordinate realizations identify the same
focus-preserving classes, on both sides. -/
theorem at_original :
    Nonempty (Focussed.Iso (S.leftAt S.focus.coordinate).focussed S.leftState.focussed) ∧
    Nonempty (Focussed.Iso (S.rightAt S.focus.coordinate).focussed S.rightState.focussed) :=
  ⟨⟨ExpansionErasure.realization_iso _ _ _ _ _ _⟩,
   ⟨ExpansionErasure.realization_iso _ _ _ _ _ _⟩⟩

theorem left_search_iff
    (away : ¬ ExpansionSearch.HoleBoundary S.focus.underlying S.focus.coordinate.val)
    (kind : Op → OperationKind) (target : State ops d) :
    State.Search kind S.leftState target ↔
      ∃ q : TypedPosition S.focus.underlying,
        SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
        Nonempty (Focussed.Iso (S.leftAt q).focussed target.focussed) :=
  ExpansionErasure.search_iff S.left S.focus S.focusCopies.1
    (fun e ne => (S.other_free e ne).1) S.left_closed
    (deepFilling_preservesSearch S.erased_edges).1 (deepFilling_searchOrigins S.erased_edges).1
    away kind target

theorem right_search_iff
    (away : ¬ ExpansionSearch.HoleBoundary S.focus.underlying S.focus.coordinate.val)
    (kind : Op → OperationKind) (target : State ops d) :
    State.Search kind S.rightState target ↔
      ∃ q : TypedPosition S.focus.underlying,
        SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
        Nonempty (Focussed.Iso (S.rightAt q).focussed target.focussed) :=
  ExpansionErasure.search_iff S.right S.focus S.focusCopies.2
    (fun e ne => (S.other_free e ne).2) S.right_closed
    (deepFilling_preservesSearch S.erased_edges).2 (deepFilling_searchOrigins S.erased_edges).2
    away kind target

/-- Recursive endpoint renaming is allowed without changing the extracted context step. -/
theorem left_deepSearch_iff
    (away : ¬ ExpansionSearch.HoleBoundary S.focus.underlying S.focus.coordinate.val)
    (kind : Op → OperationKind) (target : State ops d) :
    State.DeepSearch kind S.leftState target ↔
      ∃ q : TypedPosition S.focus.underlying,
        SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
        Nonempty (Focussed.DeepIso (S.leftAt q).focussed target.focussed) := by
  rw [State.deepSearch_iff]
  constructor
  · rintro ⟨u,h,⟨iso⟩⟩
    obtain ⟨q,step,⟨before⟩⟩ := (S.left_search_iff away kind u).mp h
    exact ⟨q,step,⟨(Focussed.DeepIso.ofIso before).trans iso⟩⟩
  · rintro ⟨q,step,iso⟩
    exact ⟨S.leftAt q,(S.left_search_iff away kind _).mpr ⟨q,step,⟨Focussed.Iso.refl _⟩⟩,iso⟩

theorem right_deepSearch_iff
    (away : ¬ ExpansionSearch.HoleBoundary S.focus.underlying S.focus.coordinate.val)
    (kind : Op → OperationKind) (target : State ops d) :
    State.DeepSearch kind S.rightState target ↔
      ∃ q : TypedPosition S.focus.underlying,
        SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
        Nonempty (Focussed.DeepIso (S.rightAt q).focussed target.focussed) := by
  rw [State.deepSearch_iff]
  constructor
  · rintro ⟨u,h,⟨iso⟩⟩
    obtain ⟨q,step,⟨before⟩⟩ := (S.right_search_iff away kind u).mp h
    exact ⟨q,step,⟨(Focussed.DeepIso.ofIso before).trans iso⟩⟩
  · rintro ⟨q,step,iso⟩
    exact ⟨S.rightAt q,(S.right_search_iff away kind _).mpr ⟨q,step,⟨Focussed.Iso.refl _⟩⟩,iso⟩

/-- Any step on one actual specimen side is matched at the same context
coordinate on the other side, provided that coordinate avoids hole boundaries. -/
theorem match_left_step
    (away : ¬ ExpansionSearch.HoleBoundary S.focus.underlying S.focus.coordinate.val)
    {kind : Op → OperationKind} {target : State ops d} (step : State.Search kind S.leftState target) :
    ∃ q : TypedPosition S.focus.underlying,
      SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
      Nonempty (Focussed.Iso (S.leftAt q).focussed target.focussed) ∧
      State.Search kind S.rightState (S.rightAt q) := by
  obtain ⟨q,h,iso⟩ := (S.left_search_iff away kind target).mp step
  exact ⟨q,h,iso,(S.right_search_iff away kind _).mpr ⟨q,h,⟨Focussed.Iso.refl _⟩⟩⟩

/-- Exact paired traversal starts at the original specimen states. -/
theorem context_steps {kind : Op → OperationKind} {n} (q : TypedPosition S.focus.underlying)
    (run : (coordinateMachine S.focus.underlying kind).Steps n S.focus.coordinate.val q.val) :
    (DeepStateClass.searchMachine kind).Steps n (DeepStateClass.ofState S.leftState)
      (DeepStateClass.ofState (S.leftAt q)) ∧
    (DeepStateClass.searchMachine kind).Steps n (DeepStateClass.ofState S.rightState)
      (DeepStateClass.ofState (S.rightAt q)) :=
  ⟨ExpansionErasure.steps S.left S.focus S.focusCopies.1
    (fun e ne => (S.other_free e ne).1) S.left_closed (deepFilling_preservesSearch S.erased_edges).1 q run,
   ExpansionErasure.steps S.right S.focus S.focusCopies.2
    (fun e ne => (S.other_free e ne).2) S.right_closed (deepFilling_preservesSearch S.erased_edges).2 q run⟩

/-- Context-only initial reachability certifies rootedness of both original states. -/
theorem rooted_of_context_run {kind : Op → OperationKind} {n}
    (run : (coordinateMachine S.focus.underlying kind).Steps n
      (TypedPosition.initial S.focus.underlying).val S.focus.coordinate.val) :
    State.Rooted kind S.leftState ∧ State.Rooted kind S.rightState :=
  ⟨ExpansionErasure.rooted S.left S.focus S.focusCopies.1
    (fun e ne => (S.other_free e ne).1) S.left_closed (deepFilling_preservesSearch S.erased_edges).1 run,
   ExpansionErasure.rooted S.right S.focus S.focusCopies.2
    (fun e ne => (S.other_free e ne).2) S.right_closed (deepFilling_preservesSearch S.erased_edges).2 run⟩

/-- Output closure excludes an exiting focus whenever both actual specimen
states are rooted: the one-edge hole path contradicts Lemma 26(3). -/
theorem not_exiting (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState) :
    ¬ S.focus.Exiting := by
  rintro ⟨e,h,label,mem⟩
  have nonop : ¬ IsOperation ops d (S.context.val.edgeLabel e) := by
    rw [label]; cases d <;> exact id
  rcases S.not_both_rooted closed (Net.Path.single e) rfl mem (List.mem_singleton_self e) nonop with bad | bad
  · exact bad left
  · exact bad right

/-- The paper's settled-mode hypotheses imply the precise boundary exclusion
needed for actual-state search reflection. -/
theorem settled_away (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    (settled : S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering)) :
    ¬ ExpansionSearch.HoleBoundary S.focus.underlying S.focus.coordinate.val := by
  intro boundary
  rcases S.focus.boundary_iff.mp boundary with ⟨mode,enters⟩ | ⟨mode,exits⟩
  · rcases settled with back | ⟨_,no⟩
    · cases back.symm.trans mode
    · exact no enters
  · exact S.not_exiting closed left right exits

/-- A settled rooted specimen's left search transition is matched on the right,
with the same erased context coordinate and an explicit left endpoint isomorphism. -/
theorem settled_match_left (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    (settled : S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering))
    {target : State ops d} (step : State.Search kind S.leftState target) :
    ∃ q : TypedPosition S.focus.underlying,
      SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
      Nonempty (Focussed.Iso (S.leftAt q).focussed target.focussed) ∧
      State.Search kind S.rightState (S.rightAt q) :=
  S.match_left_step (S.settled_away closed left right settled) step

/-- Search enabled on either settled rooted side yields synchronized transitions
on both actual sides, including arbitrary independent renaming inside boxes. -/
theorem settled_traversal (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    (settled : S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering))
    (enabled : (∃ target, State.DeepSearch kind S.leftState target) ∨
      (∃ target, State.DeepSearch kind S.rightState target)) :
    ∃ q : TypedPosition S.focus.underlying,
      SearchStep S.focus.underlying kind S.focus.coordinate.val q.val ∧
      RemotePosition S.focus.underlying q.val ∧
      State.DeepSearch kind S.leftState (S.leftAt q) ∧
      State.DeepSearch kind S.rightState (S.rightAt q) ∧
      State.Rooted kind (S.leftAt q) ∧ State.Rooted kind (S.rightAt q) := by
  have away := S.settled_away closed left right settled
  have extract : ∃ q : TypedPosition S.focus.underlying,
      SearchStep S.focus.underlying kind S.focus.coordinate.val q.val := by
    rcases enabled with ⟨target,step⟩ | ⟨target,step⟩
    · obtain ⟨q,h,_⟩ := (S.left_deepSearch_iff away kind target).mp step
      exact ⟨q,h⟩
    · obtain ⟨q,h,_⟩ := (S.right_deepSearch_iff away kind target).mp step
      exact ⟨q,h⟩
  obtain ⟨q,h⟩ := extract
  have ls := (S.left_deepSearch_iff away kind _).mpr ⟨q,h,⟨Focussed.DeepIso.refl _⟩⟩
  have rs := (S.right_deepSearch_iff away kind _).mpr ⟨q,h,⟨Focussed.DeepIso.refl _⟩⟩
  exact ⟨q,h,h.remote_target,ls,rs,DeepStateClass.rooted_search left ls,DeepStateClass.rooted_search right rs⟩

end DeepSpecimen
end Hypernets.Linear
