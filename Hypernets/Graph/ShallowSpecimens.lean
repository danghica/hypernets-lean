import Hypernets.Graph.ExpansionFocus

/-! Concrete typed pre-templates, output closure, and shallow multi-hole specimens.
Deep hole occurrences and the full UAM specimen interface remain separate. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- A type-indexed relation whose related hypernets are globally focus-free. -/
structure ConcretePreTemplate (ops : Operations Op) (d : Nat) where
  Rel : {I O : List Wire} → Hypernet ops d I O → Hypernet ops d I O → Prop
  focus_free : ∀ {I O} {G H : Hypernet ops d I O}, Rel G H → FocusFree G ∧ FocusFree H

/-- The paper's output-closure condition, applied to the concrete relation. -/
def ConcretePreTemplate.OutputClosed (T : ConcretePreTemplate ops d) : Prop :=
  ∀ {I O} {G H : Hypernet ops d I O}, T.Rel G H → OneWay G ∨ OneWay H

/-- A shallow edge is either retained by a corolla on both sides or is a
hole filled by a related pair. This describes actual graph data, not a locality law. -/
inductive SpecimenEdge (T : ConcretePreTemplate ops d) {I O} (C : Hypernet ops d I O)
    (H K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (e : C.Edge) : Prop where
  | retained : ExpansionPaths.CorollaCopy C H e → ExpansionPaths.CorollaCopy C K e → SpecimenEdge T C H K e
  | filled (h : Hole) : C.edgeLabel e = primitiveLabel ops d (.hole h) → T.Rel (H e) (K e) →
      SpecimenEdge T C H K e

/-- The fixed-depth shallow specimen restriction: a globally unique-hole
context, its retained focus, two actual simultaneous fillings, typed relation
membership at replaced holes, allowed erasure, and hole-free resulting graphs. -/
structure ShallowSpecimen (T : ConcretePreTemplate ops d)
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
  edges : ∀ e, SpecimenEdge T context.val left right e
  left_closed : HoleFree (context.val.expand left)
  right_closed : HoleFree (context.val.expand right)

/-- A focus symbol cannot be a hole label, at any available depth. -/
theorem focusLabel_ne_hole (m : Focus) (h : Hole) :
    focusLabel ops d m ≠ primitiveLabel ops d (.hole h) := by
  cases d <;> intro eq <;> cases eq

namespace ShallowSpecimen
variable {T : ConcretePreTemplate ops d} {Allowed : Hypernet ops d [.term] [] → Prop}
    (S : ShallowSpecimen T Allowed)

/-- The focus cannot fall into the filled-hole branch, so it has retained
corolla copies on both sides. -/
theorem focus_copies : Nonempty (ExpansionPaths.CorollaCopy S.context.val S.left S.focus.edge ×
    ExpansionPaths.CorollaCopy S.context.val S.right S.focus.edge) := by
  cases S.edges S.focus.edge with
  | retained l r => exact ⟨l,r⟩
  | filled h label related =>
      exact False.elim (focusLabel_ne_hole S.focus.mode h (S.focus.label.symm.trans label))

/-- Choose the retained copies certified by the preceding theorem. -/
noncomputable def focusCopies := Classical.choice S.focus_copies

/-- Every other replacement body is globally focus-free, derived from the
original unique focus and the relation's focus-free domain. -/
theorem other_free (e : S.context.val.Edge) (ne : e ≠ S.focus.edge) :
    FocusFree (S.left e) ∧ FocusFree (S.right e) := by
  cases S.edges e with
  | retained l r => exact ⟨ExpansionPaths.copy_focusFree _ _ l (S.focus.other_free e ne),
      ExpansionPaths.copy_focusFree _ _ r (S.focus.other_free e ne)⟩
  | filled h label related => exact T.focus_free related

noncomputable def leftState : State ops d :=
  ExpansionPaths.state S.left S.focus S.focusCopies.1 (fun e ne => (S.other_free e ne).1) S.left_closed

noncomputable def rightState : State ops d :=
  ExpansionPaths.state S.right S.focus S.focusCopies.2 (fun e ne => (S.other_free e ne).2) S.right_closed

/-- Concrete output closure supplies the paired path theorem's edge-wise
hypothesis; this is a proved bridge, not an assumed specimen law. -/
theorem outputClosedPair (closed : T.OutputClosed) :
    ExpansionPaths.OutputClosedPair S.context.val S.left S.right := by
  intro e
  cases S.edges e with
  | retained l r => exact Or.inl ⟨⟨l⟩,⟨r⟩⟩
  | filled h label related => exact Or.inr (closed related)

/-- Lemma 26(3) for concrete shallow multi-hole specimens. The context path
may cross any number of holes, and the one-way side may differ at each hole. -/
theorem not_both_rooted (closed : T.OutputClosed) {kind : Op → OperationKind}
    {es : List S.context.val.Edge} (path : S.context.val.Path es) {last : S.context.val.Edge}
    (endEdge : es.getLast? = some last) (target : S.focus.source ∈ S.context.val.target last)
    {bad : S.context.val.Edge} (mem : bad ∈ es)
    (nonop : ¬ IsOperation ops d (S.context.val.edgeLabel bad)) :
    ¬ State.Rooted kind S.leftState ∨ ¬ State.Rooted kind S.rightState :=
  ExpansionPaths.pair_not_rooted S.left S.right S.focus S.focusCopies.1 S.focusCopies.2
    (fun e ne => (S.other_free e ne).1) (fun e ne => (S.other_free e ne).2)
    S.left_closed S.right_closed (S.outputClosedPair closed) path endEdge target mem nonop

/-- The path consequence needed by Lemma 39(2), for this shallow specimen
representation: a context path to a jointly rooted focus has only operations. -/
theorem rooted_context_path (closed : T.OutputClosed) {kind : Op → OperationKind}
    (left : State.Rooted kind S.leftState) (right : State.Rooted kind S.rightState)
    {es : List S.context.val.Edge} (path : S.context.val.Path es) {last : S.context.val.Edge}
    (endEdge : es.getLast? = some last) (target : S.focus.source ∈ S.context.val.target last) :
    ∀ e ∈ es, IsOperation ops d (S.context.val.edgeLabel e) := by
  intro e mem
  exact (ExpansionPaths.path_operations _ _ _ (S.outputClosedPair closed) path endEdge target
    (FocusErasure.source_term S.focus) (State.rooted_focus_operationReachable left)
    (State.rooted_focus_operationReachable right) e mem).1

/-- The boundary case of Lemma 39(1) now connects directly to these concrete
simultaneous specimen states. -/
theorem boundary_agreement : (S.leftState.focussed.Initial ↔ S.rightState.focussed.Initial) ∧
    (S.leftState.focussed.Final ↔ S.rightState.focussed.Final) := by
  have l := ExpansionPaths.focussed_boundary _ _ S.focus S.focusCopies.1 (fun e ne => (S.other_free e ne).1)
  have r := ExpansionPaths.focussed_boundary _ _ S.focus S.focusCopies.2 (fun e ne => (S.other_free e ne).2)
  exact ⟨l.1.trans r.1.symm,l.2.trans r.2.symm⟩

end ShallowSpecimen
end Hypernets.Linear
