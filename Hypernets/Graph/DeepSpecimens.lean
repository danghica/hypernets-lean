import Hypernets.Graph.DeepFillings
import Hypernets.Graph.ExpansionSequential

/-! Concrete specimens with paired related holes at arbitrary box depth. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- A unique-hole focussed context, related recursive fillings of its original
holes, allowed erased context, and actual hole-free filled states. -/
structure DeepSpecimen (T : LayeredPreTemplate ops)
    (Allowed : Hypernet ops d [.term] [] → Prop) where
  context : Context ops d [.term] []
  focus : Focussed context.val
  allowed : Allowed focus.underlying
  left : (e : context.val.Edge) → Hypernet ops d
    ((alphabet ops d).signature.input (context.val.edgeLabel e))
    ((alphabet ops d).signature.output (context.val.edgeLabel e))
  right : (e : context.val.Edge) → Hypernet ops d
    ((alphabet ops d).signature.input (context.val.edgeLabel e))
    ((alphabet ops d).signature.output (context.val.edgeLabel e))
  edges : ∀ e, DeepFillingEdge T context.val left right e
  left_closed : HoleFree (context.val.expand left)
  right_closed : HoleFree (context.val.expand right)

namespace DeepSpecimen
variable {T : LayeredPreTemplate ops} {Allowed : Hypernet ops d [.term] [] → Prop}
    (S : DeepSpecimen T Allowed)

theorem filling : DeepFilling T S.context.val (S.context.val.expand S.left) (S.context.val.expand S.right) :=
  .expand _ _ _ S.edges

theorem focus_copies : Nonempty (ExpansionPaths.CorollaCopy S.context.val S.left S.focus.edge ×
    ExpansionPaths.CorollaCopy S.context.val S.right S.focus.edge) :=
  (S.edges S.focus.edge).focus_copies S.focus

noncomputable def focusCopies := Classical.choice S.focus_copies

theorem other_free (e : S.context.val.Edge) (ne : e ≠ S.focus.edge) :
    FocusFree (S.left e) ∧ FocusFree (S.right e) :=
  (S.edges e).focusFree (S.focus.other_free e ne)

noncomputable def leftState : State ops d :=
  ExpansionPaths.state S.left S.focus S.focusCopies.1 (fun e ne => (S.other_free e ne).1) S.left_closed

noncomputable def rightState : State ops d :=
  ExpansionPaths.state S.right S.focus S.focusCopies.2 (fun e ne => (S.other_free e ne).2) S.right_closed

/-- At the outer path level, rebuilt boxes are non-operation copies.
No uniform left/right one-way choice is required for the related holes. -/
theorem outputClosedPair (closed : (T d).OutputClosed) :
    ExpansionPaths.OutputClosedPair S.context.val S.left S.right :=
  fun e => (S.edges e).outputClosed closed

/-- The non-operation context-path obstruction of Lemma 26(3), now for the
recursive deep specimen representation, with actual filled states. -/
theorem not_both_rooted (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    {es : List S.context.val.Edge} (path : S.context.val.Path es) {last : S.context.val.Edge}
    (endEdge : es.getLast? = some last) (target : S.focus.source ∈ S.context.val.target last)
    {bad : S.context.val.Edge} (mem : bad ∈ es)
    (nonop : ¬ IsOperation ops d (S.context.val.edgeLabel bad)) :
    ¬ State.Rooted kind S.leftState ∨ ¬ State.Rooted kind S.rightState :=
  ExpansionPaths.pair_not_rooted S.left S.right S.focus S.focusCopies.1 S.focusCopies.2
    (fun e ne => (S.other_free e ne).1) (fun e ne => (S.other_free e ne).2)
    S.left_closed S.right_closed (S.outputClosedPair closed) path endEdge target mem nonop

/-- Joint rootedness forces every edge on a context path to the focus to be an operation. -/
theorem rooted_context_path (closed : (T d).OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    {es : List S.context.val.Edge} (path : S.context.val.Path es) {last : S.context.val.Edge}
    (endEdge : es.getLast? = some last) (target : S.focus.source ∈ S.context.val.target last) :
    ∀ e ∈ es, IsOperation ops d (S.context.val.edgeLabel e) := by
  intro e mem
  exact (ExpansionPaths.path_operations _ _ _ (S.outputClosedPair closed) path endEdge target
    (FocusErasure.source_term S.focus) (State.rooted_focus_operationReachable left)
    (State.rooted_focus_operationReachable right) e mem).1

/-- Initial/final agreement of Lemma 39(1) for recursive deep fillings. -/
theorem boundary_agreement : (S.leftState.focussed.Initial ↔ S.rightState.focussed.Initial) ∧
    (S.leftState.focussed.Final ↔ S.rightState.focussed.Final) := by
  have l := ExpansionPaths.focussed_boundary _ _ S.focus S.focusCopies.1 (fun e ne => (S.other_free e ne).1)
  have r := ExpansionPaths.focussed_boundary _ _ S.focus S.focusCopies.2 (fun e ne => (S.other_free e ne).2)
  exact ⟨l.1.trans r.1.symm,l.2.trans r.2.symm⟩

/-- The outer graph construction agrees with finite ordinary substitution.
This is a graph realization, not yet the original-hole-only tuple adequacy theorem. -/
theorem outer_realizations :
    (∃ n D, ShallowRun ops d [.term] [] S.context.val n D ∧ Nonempty (Net.Iso D S.leftState.graph)) ∧
    (∃ n D, ShallowRun ops d [.term] [] S.context.val n D ∧ Nonempty (Net.Iso D S.rightState.graph)) := by
  constructor
  · obtain ⟨n,D,_,run,iso⟩ := ExpansionSequential.realize S.context.val S.left
    exact ⟨n,D,run,iso⟩
  · obtain ⟨n,D,_,run,iso⟩ := ExpansionSequential.realize S.context.val S.right
    exact ⟨n,D,run,iso⟩

end DeepSpecimen

/-- Every previously constructed shallow specimen is a recursive specimen. -/
def ShallowSpecimen.toDeep {T : LayeredPreTemplate ops}
    {Allowed : Hypernet ops d [.term] [] → Prop} (S : ShallowSpecimen (T d) Allowed) :
    DeepSpecimen T Allowed where
  context := S.context
  focus := S.focus
  allowed := S.allowed
  left := S.left
  right := S.right
  edges e := (S.edges e).deep
  left_closed := S.left_closed
  right_closed := S.right_closed

end Hypernets.Linear
