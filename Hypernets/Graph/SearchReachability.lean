import Hypernets.Graph.StateRoots

/-! Operation reachability is an invariant of coordinate search. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    {G H : Hypernet ops d I O}

/-- A vertex is reachable from some input using only actual operation edges. -/
def OperationReachable (G : Hypernet ops d I O) (v : G.Vertex) : Prop :=
  ∃ i es, G.OperationTrace (IsOperation ops d) v es (.input i)

theorem OperationReachable.input (i : Fin I.length) : OperationReachable G (.input i) :=
  ⟨i, [], .nil _⟩

theorem SearchOperation.isOperation (a : SearchOperation G) : IsOperation ops d (G.edgeLabel a.edge) := by
  rw [a.label]
  cases d <;> trivial

/-- Traversing an argument extends the input-to-source operation path. -/
theorem OperationReachable.argument (a : SearchOperation G) {v : G.Vertex}
    (root : OperationReachable G a.source) (arg : v ∈ a.arguments) : OperationReachable G v := by
  obtain ⟨i, es, trace⟩ := root
  exact ⟨i, a.edge :: es, .cons a.isOperation (a.argument_mem arg)
    (by rw [a.source_eq]; simp) trace⟩

/-- Any operation targeting a reachable vertex has a reachable source. -/
theorem OperationReachable.source (a : SearchOperation G) {v : G.Vertex}
    (root : OperationReachable G v) (arg : v ∈ a.arguments) : OperationReachable G a.source := by
  obtain ⟨i, es, trace⟩ := root
  cases trace with
  | nil => exact False.elim (G.target_not_input (a.argument_mem arg) trivial)
  | cons op target source tail =>
      have eq := G.target_unique target (a.argument_mem arg)
      subst eq
      rw [a.source_eq] at source
      have same := List.mem_singleton.mp source
      subst same
      exact ⟨i, _, tail⟩

/-- All five search rules preserve operation reachability of the coordinate. -/
theorem SearchStep.operationReachable {kind : Op → OperationKind} {p q : SearchPosition G}
    (step : SearchStep G kind p q) (root : OperationReachable G p.2) : OperationReachable G q.2 := by
  cases step with
  | trigger => exact root
  | enter a =>
      simp only [SearchOperation.enter]
      split
      next empty => exact root
      next v vs eq => exact root.argument a (by simp [eq])
  | resume a i v arg =>
      have parent := root.source a (List.mem_of_getElem? arg)
      simp only [SearchOperation.resume]
      split
      next w nextArg => exact parent.argument a (List.mem_of_getElem? nextArg)
      next none => exact parent

/-- Recursive renaming carries operation reachability forwards. -/
theorem OperationReachable.rename (a : DeepIso G H) {v : G.Vertex}
    (root : OperationReachable G v) : OperationReachable H (Port.map a.vertices.toFun v) := by
  obtain ⟨i, es, trace⟩ := root
  exact ⟨i, es.map a.edges.toFun, a.operationTrace trace⟩

theorem OperationReachable.rename_iff (a : DeepIso G H) (v : G.Vertex) :
    OperationReachable H (Port.map a.vertices.toFun v) ↔ OperationReachable G v := by
  constructor
  · intro root
    have h := root.rename (DeepIso.symm a)
    simpa only [show Port.map (DeepIso.symm a).vertices.toFun (Port.map a.vertices.toFun v) = v
      from (Port.bijection a.vertices).left_inv v] using h
  · exact rename a

end Hypernets.Linear
