import Hypernets.Graph.SearchQuotientExecutions

/-! The initial state on the erased underlying graph, and its invariant
isomorphism class. This is the root used in the paper's definition of rootedness. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace State

/-- Attach an initial search focus to the state's own erased underlying graph. -/
noncomputable def root (s : State ops d) : State ops d :=
  (TypedPosition.initial s.focussed.underlying).realize s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free)

theorem root_initial (s : State ops d) : (root s).focussed.Initial :=
  TypedPosition.initial_realize _ _

/-- Initial attachment respects a recursive isomorphism of underlying graphs. -/
noncomputable def root_of_underlying {s t : State ops d}
    (a : DeepIso s.focussed.underlying t.focussed.underlying) :
    Focussed.DeepIso (root s).focussed (root t).focussed :=
  TypedPosition.realize_deepRename a (TypedPosition.initial s.focussed.underlying)
    s.focussed.underlying_focusFree (s.focussed.underlying_holeFree s.hole_free)
    t.focussed.underlying_focusFree (t.focussed.underlying_holeFree t.hole_free)

noncomputable def root_iso {s t : State ops d} (a : Focussed.DeepIso s.focussed t.focussed) :
    Focussed.DeepIso (root s).focussed (root t).focussed := root_of_underlying a.erased

/-- An initial state's extracted coordinate is exactly search at its sole input. -/
theorem coordinate_initial {s : State ops d} (initial : s.focussed.Initial) :
    coordinate s = TypedPosition.initial s.focussed.underlying := by
  have h := (coordinate_boundary s).1.mpr initial
  apply Subtype.ext
  apply Prod.ext
  · exact h.1
  · cases eq : (coordinate s).val.2 with
    | internal v => rw [eq] at h; exact False.elim h.2
    | input i => have hi : i = 0 := Fin.ext (by have hlt : i.val < 1 := i.isLt; change i.val = 0; omega); subst i; rfl
    | output i => exact Fin.elim0 i

/-- Reattaching the initial focus recovers any already initial state. -/
noncomputable def root_initial_iso {s : State ops d} (initial : s.focussed.Initial) :
    Focussed.DeepIso (root s).focussed s.focussed := by
  have h := Focussed.DeepIso.ofIso (recover s)
  rw [coordinate_initial initial] at h
  exact h

/-- Search changes the focus position but preserves the whole underlying graph
up to recursive isomorphism. -/
theorem deepSearch_underlying {kind : Op → OperationKind} {s t : State ops d}
    (step : DeepSearch kind s t) : Nonempty (DeepIso s.focussed.underlying t.focussed.underlying) := by
  obtain ⟨q, _, ⟨qt⟩⟩ := step
  let cancel := FocusInsertion.underlying_iso s.focussed.underlying q.val.2 q.property
    q.not_output q.val.1 s.focussed.underlying_focusFree
  exact ⟨DeepIso.trans (DeepIso.symm (DeepIso.ofIso cancel)) qt.erased⟩

end State

namespace DeepStateClass

/-- The canonical initial class with the same erased underlying graph. -/
noncomputable def root (s : DeepStateClass ops d) : DeepStateClass ops d :=
  Quotient.liftOn s (fun s => ofState (State.root s))
    (fun _ _ ⟨a⟩ => Quotient.sound ⟨State.root_iso a⟩)

theorem root_ofState (s : State ops d) : root (ofState s) = ofState (State.root s) := rfl

theorem root_initial (s : DeepStateClass ops d) : Initial (root s) := by
  induction s using Quotient.inductionOn with
  | h s => exact State.root_initial s

theorem root_eq_of_initial {s : DeepStateClass ops d} (initial : Initial s) : root s = s := by
  induction s using Quotient.inductionOn with
  | h s => exact Quotient.sound ⟨State.root_initial_iso initial⟩

theorem root_idempotent (s : DeepStateClass ops d) : root (root s) = root s :=
  root_eq_of_initial (root_initial s)

/-- Every search transition retains the same canonical initial class. -/
theorem search_root {kind : Op → OperationKind} {s t : DeepStateClass ops d}
    (step : Search kind s t) : root s = root t := by
  induction s, t using Quotient.inductionOn₂ with
  | h s t =>
      obtain ⟨a⟩ := State.deepSearch_underlying step
      exact Quotient.sound ⟨State.root_of_underlying a⟩

theorem steps_root {kind : Op → OperationKind} {n} {s t : DeepStateClass ops d}
    (run : (searchMachine kind).Steps n s t) : root s = root t := by
  induction run with
  | zero => rfl
  | cons step _ ih => exact (search_root step).trans ih

/-- The paper's rooted condition: search reachability from one's own initial attachment. -/
def Rooted (kind : Op → OperationKind) (s : DeepStateClass ops d) : Prop :=
  ∃ n, (searchMachine kind).Steps n (root s) s

theorem initial_rooted {kind : Op → OperationKind} {s : DeepStateClass ops d}
    (initial : Initial s) : Rooted kind s := by
  refine ⟨0, ?_⟩
  rw [root_eq_of_initial initial]
  exact .zero _

theorem root_rooted (kind : Op → OperationKind) (s : DeepStateClass ops d) : Rooted kind (root s) :=
  initial_rooted (root_initial s)

/-- Search preserves rootedness without assuming refocusing of an external machine. -/
theorem rooted_search {kind : Op → OperationKind} {s t : DeepStateClass ops d}
    (rooted : Rooted kind s) (step : Search kind s t) : Rooted kind t := by
  obtain ⟨n, run⟩ := rooted
  refine ⟨n+1, ?_⟩
  rw [← search_root step]
  exact run.append (.cons step (.zero _))

theorem rooted_steps {kind : Op → OperationKind} {n} {s t : DeepStateClass ops d}
    (rooted : Rooted kind s) (run : (searchMachine kind).Steps n s t) : Rooted kind t := by
  induction run with
  | zero => exact rooted
  | cons step _ ih => exact ih (rooted_search rooted step)

end DeepStateClass
end Hypernets.Linear
