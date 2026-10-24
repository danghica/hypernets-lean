import Hypernets.Graph.RootedStatePaths

/-! The rooted-path obstruction for the original nonempty edge-path datatype. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    {G : Hypernet ops d I O}

/-- An incoming edge at a reachable vertex is an operation, even before
choosing any source of that edge. -/
theorem OperationReachable.incoming_operation {v : G.Vertex} {e : G.Edge}
    (root : OperationReachable G v) (target : v ∈ G.target e) : IsOperation ops d (G.edgeLabel e) := by
  obtain ⟨i, es, trace⟩ := root
  cases trace with
  | nil => exact False.elim (G.target_not_input target trivial)
  | cons op target' source tail =>
      have eq := G.target_unique target target'
      subst eq
      exact op

/-- Along any edge path ending at a reachable vertex, all edges are operations
and every source vertex is itself reachable from an input. -/
theorem path_operations_of_reachable {es : List G.Edge} (path : G.Path es)
    {last : G.Edge} (endEdge : es.getLast? = some last) {v : G.Vertex}
    (target : v ∈ G.target last) (root : OperationReachable G v) :
    ∀ e ∈ es, IsOperation ops d (G.edgeLabel e) ∧
      ∀ w ∈ G.source e, OperationReachable G w := by
  induction path with
  | single e =>
      have eq : e = last := by simpa using endEdge
      subst last
      intro f mem
      have eq := List.mem_singleton.mp mem
      subst f
      exact ⟨root.incoming_operation target, fun w hw => (root.predecessor target hw).2⟩
  | @cons e f es adjacent path ih =>
      have rest := ih (by simpa using endEdge)
      obtain ⟨w, we, wf⟩ := adjacent
      have reach := (rest f (by simp)).2 w wf
      intro g mem
      cases List.mem_cons.mp mem with
      | inl eq =>
          subst g
          exact ⟨reach.incoming_operation we, fun x hx => (reach.predecessor we hx).2⟩
      | inr mem => exact rest g mem

namespace State
variable {s : State ops d} {kind : Op → OperationKind}

/-- Lemma 26(1) for the existing edge-path notion, allowing repeated edges:
every edge of a path arriving at a rooted focus source is an operation. -/
theorem rooted_path_operations (rooted : Rooted kind s) {es : List s.graph.Edge}
    (path : s.graph.Path es) {last : s.graph.Edge} (endEdge : es.getLast? = some last)
    (target : s.focussed.source ∈ s.graph.target last) :
    ∀ e ∈ es, IsOperation ops d (s.graph.edgeLabel e) := by
  intro e mem
  exact (path_operations_of_reachable path endEdge target (rooted_focus_operationReachable rooted) e mem).1

/-- A path containing any non-operation edge and ending at the focus source
is a concrete, checkable certificate that the state is not rooted. -/
theorem not_rooted_of_path {es : List s.graph.Edge} (path : s.graph.Path es)
    {last : s.graph.Edge} (endEdge : es.getLast? = some last)
    (target : s.focussed.source ∈ s.graph.target last)
    {e : s.graph.Edge} (mem : e ∈ es) (bad : ¬ IsOperation ops d (s.graph.edgeLabel e)) :
    ¬ Rooted kind s := fun rooted => bad (rooted_path_operations rooted path endEdge target e mem)

end State
end Hypernets.Linear
