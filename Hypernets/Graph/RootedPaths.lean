import Hypernets.Graph.SearchReachability

/-! Incoming paths to operation-reachable vertices, and lifting them through
focus insertion. These are the graph-theoretic steps behind Appendix C. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    {G : Hypernet ops d I O}

/-- Reverse incidence trace without any restriction on edge labels. -/
inductive IncomingTrace (G : Hypernet ops d I O) : G.Vertex → List G.Edge → G.Vertex → Prop where
  | nil (v) : IncomingTrace G v [] v
  | cons {v w z e es} (target : v ∈ G.target e) (source : w ∈ G.source e)
      (tail : IncomingTrace G w es z) : IncomingTrace G v (e :: es) z

/-- Any incoming edge at an operation-reachable vertex must itself be an
operation, and each of its sources is operation-reachable. -/
theorem OperationReachable.predecessor {v w : G.Vertex} {e : G.Edge}
    (root : OperationReachable G v) (target : v ∈ G.target e) (source : w ∈ G.source e) :
    IsOperation ops d (G.edgeLabel e) ∧ OperationReachable G w := by
  obtain ⟨i, es, trace⟩ := root
  cases trace with
  | nil => exact False.elim (G.target_not_input target trivial)
  | @cons v z _ f fs op ft src tail =>
      have ef := G.target_unique target ft
      subst f
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (unary_operations ops d G e op)
      rw [hx] at source src
      have eq := (List.mem_singleton.mp source).trans (List.mem_singleton.mp src).symm
      subst z
      exact ⟨op, i, fs, tail⟩

/-- Every path arriving at an operation-reachable vertex is an operation path. -/
theorem IncomingTrace.operations {v w : G.Vertex} {es}
    (trace : IncomingTrace G v es w) (root : OperationReachable G v) :
    G.OperationTrace (IsOperation ops d) v es w := by
  induction trace with
  | nil => exact .nil _
  | cons target source tail ih =>
      obtain ⟨op, parent⟩ := root.predecessor target source
      exact .cons op target source (ih parent)

/-- In a reverse operation trace no source can return to a vertex whose
input distance is at least the length of that trace. -/
theorem operationTrace_sources_avoid {v z : G.Vertex} {i j : Fin I.length} {fs es}
    (root : G.OperationTrace (IsOperation ops d) v fs (.input i))
    (trace : G.OperationTrace (IsOperation ops d) z es (.input j))
    (bound : es.length ≤ fs.length) : ∀ e ∈ es, v ∉ G.source e := by
  induction es generalizing z with
  | nil => simp
  | cons e es ih =>
    cases trace with
    | cons op target source tail =>
      intro f mem hit
      cases List.mem_cons.mp mem with
      | inl eq =>
          subst f
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (unary_operations ops d G e op)
          rw [hx] at source hit
          have eq := (List.mem_singleton.mp source).trans (List.mem_singleton.mp hit).symm
          subst eq
          have lengths := (Net.OperationTrace.unique_to_inputs G (IsOperation ops d)
            (unary_operations ops d G) root tail trivial trivial).1
          have count := congrArg List.length lengths
          simp only [List.length_cons] at bound
          omega
      | inr mem =>
          exact ih tail (by simp only [List.length_cons] at bound; omega) f mem hit

/-- An input-to-v operation path survives inserting a focus at v: the path
never departs from v earlier, so no source on it is split away from its host. -/
theorem operationTrace_insert {I : List Wire} {G : Hypernet ops d I []}
    (v : G.Vertex) (term : G.vertexLabel v = .term) (notOutput : ¬ v.IsOutput) (mode : Focus)
    {i : Fin I.length} {es}
    (trace : G.OperationTrace (IsOperation ops d) v es (.input i)) :
    (FocusInsertion.insert G v term notOutput mode).OperationTrace (IsOperation ops d)
      (FocusInsertion.host G v) (es.map Sum.inl) (.input i) := by
  have avoid := operationTrace_sources_avoid trace trace (Nat.le_refl _)
  have lift : ∀ {x y : G.Vertex} {fs}, G.OperationTrace (IsOperation ops d) x fs y →
      (∀ e ∈ fs, v ∉ G.source e) →
      (FocusInsertion.insert G v term notOutput mode).OperationTrace (IsOperation ops d)
        (FocusInsertion.host G x) (fs.map Sum.inl) (FocusInsertion.host G y) := by
    intro x y fs path
    induction path with
    | nil => intro _; exact .nil _
    | @cons x w y e fs op target source tail ih =>
        intro no
        have ne : w ≠ v := fun eq => no e (by simp) (eq ▸ source)
        apply Net.OperationTrace.cons (G := FocusInsertion.insert G v term notOutput mode)
          (e := Sum.inl e) (w := FocusInsertion.host G w) op
        · exact List.mem_map_of_mem target
        · apply List.mem_map.mpr
          exact ⟨w, source, by simp [FocusInsertion.split, ne]⟩
        · exact ih (fun e mem => no e (List.mem_cons_of_mem _ mem))
  exact lift trace avoid

end Hypernets.Linear
