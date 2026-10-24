import Hypernets.Graph.RootedPathObstruction

/-! One-way hypernets and extraction of operation paths from shallow fillings. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    {G : Hypernet ops d I O}

/-- Every source of an actual operation has term type. -/
theorem operation_source_term {e : G.Edge} (op : IsOperation ops d (G.edgeLabel e))
    {v : G.Vertex} (source : v ∈ G.source e) : G.vertexLabel v = .term := by
  have typed : G.vertexLabel v ∈ (alphabet ops d).signature.input (G.edgeLabel e) := by
    rw [← G.source_typed e]
    exact List.mem_map_of_mem source
  cases d with
  | zero =>
      cases label : G.edgeLabel e with
      | up p => cases p <;> simp_all [IsOperation, alphabet, baseAlphabet, primitiveSignature]
  | succ n =>
      cases label : G.edgeLabel e with
      | inl p => cases p <;> simp_all [IsOperation, alphabet, nextAlphabet, primitiveSignature]
      | inr b => simp [IsOperation, label] at op

/-- A nonempty operation trace ending at an input necessarily starts there
from a term-typed input. -/
theorem operationTrace_input_term {v : G.Vertex} {es : List G.Edge} {i : Fin I.length}
    (trace : G.OperationTrace (IsOperation ops d) v es (.input i)) (nonempty : es ≠ []) :
    G.vertexLabel (.input i) = .term := by
  induction es generalizing v with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
      cases trace with
      | cons op target source tail =>
          cases es with
          | nil => cases tail; exact operation_source_term op source
          | cons f fs => exact ih tail (by simp)

/-- The paper's term-to-term restriction: no operation path runs from a term
input to a term output. -/
def OneWay (G : Hypernet ops d I O) : Prop :=
  ∀ (i : Fin I.length) (j : Fin O.length),
    G.vertexLabel (.input i) = .term → G.vertexLabel (.output j) = .term →
    ∀ es, ¬ G.OperationPath (IsOperation ops d) (.input i) es (.output j)

/-- Equivalently, no term output is operation-reachable from any input. -/
theorem oneWay_iff : OneWay G ↔ ∀ j : Fin O.length,
    G.vertexLabel (.output j) = .term → ¬ OperationReachable G (.output j) := by
  constructor
  · intro one j term ⟨i, es, trace⟩
    have nonempty : es ≠ [] := by intro eq; subst es; cases trace
    exact one i j (operationTrace_input_term trace nonempty) term es.reverse (by
      simpa [Net.OperationPath] using trace)
  · intro one i j _ term es path
    exact one j term ⟨i, es.reverse, path⟩

/-- Decompose a nonempty reverse operation trace at its first edge. -/
theorem operationTrace_cons_iff {v z : G.Vertex} {e : G.Edge} {es} :
    G.OperationTrace (IsOperation ops d) v (e :: es) z ↔
      ∃ w, IsOperation ops d (G.edgeLabel e) ∧ v ∈ G.target e ∧
        w ∈ G.source e ∧ G.OperationTrace (IsOperation ops d) w es z := by
  constructor
  · intro h; cases h with | cons op target source tail => exact ⟨_, op, target, source, tail⟩
  · rintro ⟨w, op, target, source, tail⟩; exact .cons op target source tail

/-- Independent recursive renaming preserves and reflects one-wayness. -/
theorem DeepIso.oneWay_iff {H : Hypernet ops d I O} (a : DeepIso G H) :
    OneWay G ↔ OneWay H := by
  rw [Linear.oneWay_iff, Linear.oneWay_iff]
  constructor
  · intro one j term reach
    exact one j term ((OperationReachable.rename_iff a (.output j)).mp reach)
  · intro one j term reach
    exact one j term (reach.rename a)

/-- A graph with no outputs is one-way, vacuously. -/
theorem oneWay_no_outputs {G : Hypernet ops d I []} : OneWay G := by
  intro i j
  exact Fin.elim0 j

namespace OneWayReplacement
variable (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
open Net.Replacement

/-- An inserted non-input cannot become an input of the filled graph. This
uses target coverage, and holds even when the hole has a self-loop. -/
theorem insert_not_input {v : H.Vertex} (notInput : ¬ v.IsInput) :
    ¬ (insert C hole H v).IsInput := by
  obtain ⟨e, target⟩ := (H.target_coverage v).mpr notInput
  exact (C.plug hole H).target_not_input
    (e := Sum.inr e) (List.mem_map_of_mem target)

/-- If an inserted vertex is operation-reachable in the whole filling, it is
operation-reachable inside the filling itself. The extracted prefix ends as
soon as it reaches a filling input; no injectivity of the entire insertion
map, and hence no non-self-loop assumption, is needed. -/
theorem extract {v : H.Vertex} (root : OperationReachable (C.plug hole H) (insert C hole H v)) :
    OperationReachable H v := by
  obtain ⟨i, es, trace⟩ := root
  induction es generalizing v with
  | nil =>
      have eq := trace.steps.zero_eq
      by_cases input : v.IsInput
      · cases v with
        | input j => exact .input j
        | internal => contradiction
        | output => contradiction
      · exact False.elim (insert_not_input C hole H input (eq ▸ trivial))
  | cons e es ih =>
      obtain ⟨w, op, target, source, tail⟩ := operationTrace_cons_iff.mp trace
      by_cases input : v.IsInput
      · cases v with
        | input j => exact .input j
        | internal => contradiction
        | output => contradiction
      · obtain ⟨f, ft⟩ := (H.target_coverage v).mpr input
        have inserted : insert C hole H v ∈ (C.plug hole H).target (Sum.inr f) :=
          List.mem_map_of_mem ft
        have ef : e = Sum.inr f := (C.plug hole H).target_unique target inserted
        subst e
        obtain ⟨x, hx, xe⟩ := List.mem_map.mp source
        obtain ⟨j, fs, inside⟩ := ih (v := x) (xe.symm ▸ tail)
        exact ⟨j, f :: fs, .cons op ft hx inside⟩

/-- One-way fillings cannot account for an operation-reachable term vertex
of the host: its operation path already exists in the unfilled host. -/
theorem reflect (one : OneWay H) {v : C.Vertex} (term : C.vertexLabel v = .term)
    (root : OperationReachable (C.plug hole H) (host C hole H v)) :
    OperationReachable C v := by
  obtain ⟨i, es, trace⟩ := root
  induction es generalizing v with
  | nil =>
      have eq : host C hole H v = host C hole H (.input i) := trace.steps.zero_eq
      have same := host_injective C hole H eq
      exact same ▸ OperationReachable.input i
  | cons e es ih =>
      obtain ⟨w, op, target, source, tail⟩ := operationTrace_cons_iff.mp trace
      cases e with
      | inl e =>
          obtain ⟨x, hx, xv⟩ := List.mem_map.mp target
          have same := host_injective C hole H xv
          subst x
          obtain ⟨y, hy, yw⟩ := List.mem_map.mp source
          have parent := ih (operation_source_term (G := C) (e := e.val) op hy) (yw.symm ▸ tail)
          obtain ⟨j, fs, inside⟩ := parent
          exact ⟨j, e.val :: fs, .cons op hx hy inside⟩
      | inr e =>
          obtain ⟨x, hx, xv⟩ := List.mem_map.mp target
          obtain ⟨j, rfl, port⟩ := insert_target_host C hole H (H.target_not_input hx) xv
          have reach : OperationReachable (C.plug hole H) (insert C hole H (.output j)) :=
            xv.symm ▸ (show OperationReachable (C.plug hole H) (host C hole H v) from
              ⟨i, Sum.inr e :: es, trace⟩)
          have outputTerm : H.vertexLabel (.output j) = .term := by
            have labels := insert_label C hole H (.output j)
            rw [xv, host_label C hole H, term] at labels
            exact labels.symm
          exact False.elim ((oneWay_iff.mp one) j outputTerm (extract C hole H reach))

/-- Every incoming host path to such a reachable term vertex consists of
operations, even if the supplied path passes through the replaced edge. -/
theorem path_operations (one : OneWay H) {v : C.Vertex} (term : C.vertexLabel v = .term)
    (root : OperationReachable (C.plug hole H) (host C hole H v))
    {es : List C.Edge} (path : C.Path es) {last : C.Edge}
    (endEdge : es.getLast? = some last) (target : v ∈ C.target last) :
    ∀ e ∈ es, IsOperation ops d (C.edgeLabel e) := by
  intro e mem
  exact (path_operations_of_reachable path endEdge target (reflect C hole H one term root) e mem).1

/-- One-wayness is closed under shallow filling by another one-way hypernet. -/
theorem oneWay_plug (hostOne : OneWay C) (fillOne : OneWay H) :
    OneWay (C.plug hole H) := by
  apply oneWay_iff.mpr
  intro j term reach
  exact (oneWay_iff.mp hostOne) j term
    (reflect C hole H fillOne term reach)

end OneWayReplacement
end Hypernets.Linear
