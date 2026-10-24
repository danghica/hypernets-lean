import Hypernets.Graph.RootedPaths

/-! Rooted states have operation-reachable focus sources. Every incoming path
to such a source is an operation path (Appendix C, Lemmas 23 and 26(1)). -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace State

/-- Operation reachability of the focus coordinate in the erased graph. -/
def UnderlyingReachable (s : State ops d) : Prop :=
  OperationReachable s.focussed.underlying (coordinate s).val.2

theorem underlyingReachable_iso {s t : State ops d} (a : Focussed.DeepIso s.focussed t.focussed) :
    UnderlyingReachable s ↔ UnderlyingReachable t := by
  have h := OperationReachable.rename_iff a.erased (coordinate s).val.2
  have eq := congrArg (fun p => p.val.2) (coordinate_deepIso a)
  change Port.map a.erased.vertices.toFun (coordinate s).val.2 = (coordinate t).val.2 at eq
  rw [eq] at h
  exact h.symm

/-- Realization retains a coordinate's operation reachability after erasure. -/
theorem underlyingReachable_realize {G : Hypernet ops d [.term] []} (p : TypedPosition G)
    (fg : FocusFree G) (hg : HoleFree G) (reach : OperationReachable G p.val.2) :
    UnderlyingReachable (p.realize fg hg) := by
  obtain ⟨a, eq⟩ := p.coordinate_recovery fg hg
  have pos := congrArg (fun p => p.val.2) eq
  change Port.map a.vertices.toFun (coordinate (p.realize fg hg)).val.2 = p.val.2 at pos
  apply (OperationReachable.rename_iff (DeepIso.ofIso a) _).mp
  change OperationReachable G (Port.map a.vertices.toFun (coordinate (p.realize fg hg)).val.2)
  rw [pos]
  exact reach

theorem root_underlyingReachable (s : State ops d) : UnderlyingReachable (root s) :=
  underlyingReachable_realize _ _ _ (OperationReachable.input (G := s.focussed.underlying) 0)

/-- The operation-reachability invariant survives every recursively renamed search step. -/
theorem deepSearch_underlyingReachable {kind : Op → OperationKind} {s t : State ops d}
    (reach : UnderlyingReachable s) (step : DeepSearch kind s t) : UnderlyingReachable t := by
  obtain ⟨q, step, ⟨qt⟩⟩ := step
  exact (underlyingReachable_iso qt).mp (underlyingReachable_realize q _ _ (step.operationReachable reach))

/-- Lift the operation path to the actual focussed state, not merely its erasure. -/
theorem focus_operationReachable {s : State ops d} (reach : UnderlyingReachable s) :
    OperationReachable s.graph s.focussed.source := by
  obtain ⟨i, es, trace⟩ := reach
  let p := coordinate s
  have lifted := operationTrace_insert p.val.2 p.property p.not_output p.val.1 trace
  let a := recover s
  have path := (DeepIso.ofIso a.graph).operationTrace lifted
  change s.graph.OperationTrace (IsOperation ops d)
    (Port.map a.graph.vertices.toFun (FocusInsertion.host s.focussed.underlying p.val.2))
    ((es.map Sum.inl).map a.graph.edges.toFun) (.input i) at path
  have src := a.source
  change Port.map a.graph.vertices.toFun (FocusInsertion.host s.focussed.underlying p.val.2) =
    s.focussed.source at src
  rw [src] at path
  exact ⟨i, _, path⟩

end State

namespace DeepStateClass

/-- The invariant is well-defined on recursive state classes. -/
def UnderlyingReachable (s : DeepStateClass ops d) : Prop :=
  Quotient.liftOn s State.UnderlyingReachable
    (fun _ _ ⟨a⟩ => propext (State.underlyingReachable_iso a))

theorem root_underlyingReachable (s : DeepStateClass ops d) : UnderlyingReachable (root s) := by
  induction s using Quotient.inductionOn with
  | h s => exact State.root_underlyingReachable s

theorem search_underlyingReachable {kind : Op → OperationKind} {s t : DeepStateClass ops d}
    (reach : UnderlyingReachable s) (step : Search kind s t) : UnderlyingReachable t := by
  induction s, t using Quotient.inductionOn₂ with
  | h s t => exact State.deepSearch_underlyingReachable reach step

/-- Rootedness supplies the operation-reachability invariant by induction on the root run. -/
theorem rooted_underlyingReachable {kind : Op → OperationKind} {s : DeepStateClass ops d}
    (rooted : Rooted kind s) : UnderlyingReachable s := by
  obtain ⟨n, run⟩ := rooted
  have invariant : ∀ {x y : DeepStateClass ops d} {m},
      (searchMachine kind).Steps m x y → UnderlyingReachable x → UnderlyingReachable y := by
    intro x y m run
    induction run with
    | zero => exact id
    | cons step _ ih => exact fun h => ih (search_underlyingReachable h step)
  exact invariant run (root_underlyingReachable s)

end DeepStateClass

namespace State

/-- A concrete state's recursive isomorphism class is rooted. -/
def Rooted (kind : Op → OperationKind) (s : State ops d) : Prop :=
  DeepStateClass.Rooted kind (DeepStateClass.ofState s)

/-- Concrete version of Lemma 23: the actual focus source lies on an operation path from an input. -/
theorem rooted_focus_operationReachable {kind : Op → OperationKind} {s : State ops d}
    (rooted : Rooted kind s) : OperationReachable s.graph s.focussed.source :=
  focus_operationReachable (DeepStateClass.rooted_underlyingReachable rooted)

/-- The path starts at the state's unique input and is nonempty whenever the
focus source is not that input, as in the paper's statement of Lemma 23. -/
theorem rooted_focus_path {kind : Op → OperationKind} {s : State ops d}
    (rooted : Rooted kind s) :
    ∃ es, s.graph.OperationPath (IsOperation ops d) (.input 0) es s.focussed.source ∧
      (¬ s.focussed.source.IsInput → es ≠ []) := by
  obtain ⟨i, es, trace⟩ := rooted_focus_operationReachable rooted
  have hi : i = 0 := Fin.ext (by have h : i.val < 1 := i.isLt; change i.val = 0; omega)
  subst i
  refine ⟨es.reverse, ?_, ?_⟩
  · simpa only [Net.OperationPath, List.reverse_reverse] using trace
  · intro noninput empty
    have nil : es = [] := by simpa using congrArg List.reverse empty
    subst es
    have eq := trace.steps.zero_eq
    apply noninput
    rw [eq]
    trivial

/-- Every incoming incidence path to a rooted focus source uses operation edges only. -/
theorem rooted_incoming_operations {kind : Op → OperationKind} {s : State ops d}
    (rooted : Rooted kind s) {v : s.graph.Vertex} {es}
    (path : IncomingTrace s.graph s.focussed.source es v) :
    s.graph.OperationTrace (IsOperation ops d) s.focussed.source es v :=
  path.operations (rooted_focus_operationReachable rooted)

/-- Concrete Lemma 26(1): a non-operation path arriving at the focus source
rules out rootedness. The path may start anywhere in the graph. -/
theorem not_rooted_of_nonoperation_path {kind : Op → OperationKind} {s : State ops d}
    {v : s.graph.Vertex} {es} (path : IncomingTrace s.graph s.focussed.source es v)
    (bad : ¬ s.graph.OperationTrace (IsOperation ops d) s.focussed.source es v) :
    ¬ Rooted kind s := fun rooted => bad (rooted_incoming_operations rooted path)

end State
end Hypernets.Linear
