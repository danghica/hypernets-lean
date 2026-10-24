import Hypernets.Graph.Simultaneous
import Hypernets.Graph.OneWayObstruction

/-! Actual path extraction and paired host-path reflection for simultaneous fillings. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
namespace ExpansionPaths
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
open Net.Expansion

/-- A literal corolla copy of a host edge, allowing an arbitrary name for its
single edge. Its incidences are the full ordered boundary, and no other edges exist. -/
structure CorollaCopy (e : C.Edge) where
  edge : (H e).Edge
  label : (H e).edgeLabel edge = C.edgeLabel e
  source : (H e).source edge = (List.finRange _).map Port.input
  target : (H e).target edge = (List.finRange _).map Port.output
  only : ∀ x, x = edge

/-- Supplying the existing corolla constructor gives an unchanged edge. -/
def corollaCopy (e : C.Edge) : CorollaCopy C
    (fun e => Net.corolla (alphabet ops d).signature (C.edgeLabel e)) e where
  edge := 0
  label := rfl
  source := rfl
  target := rfl
  only x := Fin.ext (by have h : x.val < 1 := x.isLt; omega)

theorem copy_source {e : C.Edge} (copy : CorollaCopy C H e) {v : C.Vertex}
    (mem : v ∈ C.source e) : host C H v ∈ (C.expand H).source ⟨e,copy.edge⟩ := by
  obtain ⟨i, rfl⟩ := (C.mem_source_iff_port e v).mp mem
  refine List.mem_map.mpr ⟨.input i, ?_, rfl⟩
  rw [copy.source]
  exact List.mem_map_of_mem (List.mem_finRange i)

theorem copy_target {e : C.Edge} (copy : CorollaCopy C H e) {v : C.Vertex}
    (mem : v ∈ C.target e) : host C H v ∈ (C.expand H).target ⟨e,copy.edge⟩ := by
  obtain ⟨i, rfl⟩ := (C.mem_target_iff_port e v).mp mem
  refine List.mem_map.mpr ⟨.output i, ?_, rfl⟩
  rw [copy.target]
  exact List.mem_map_of_mem (List.mem_finRange i)

/-- Non-input vertices of any individual filling cannot become global inputs. -/
theorem insert_not_input (e : C.Edge) {v : (H e).Vertex} (notInput : ¬ v.IsInput) :
    ¬ (insert C H e v).IsInput := by
  obtain ⟨f, target⟩ := ((H e).target_coverage v).mpr notInput
  exact (C.expand H).target_not_input (e := ⟨e,f⟩) (List.mem_map_of_mem target)

/-- Extract a local operation path from an operation-reachable inserted
vertex, irrespective of the contents of every other simultaneous filling. -/
theorem extract (e : C.Edge) {v : (H e).Vertex}
    (root : OperationReachable (C.expand H) (insert C H e v)) : OperationReachable (H e) v := by
  obtain ⟨i, es, trace⟩ := root
  induction es generalizing v with
  | nil =>
      have eq := trace.steps.zero_eq
      by_cases input : v.IsInput
      · cases v with
        | input j => exact .input j
        | internal => contradiction
        | output => contradiction
      · exact False.elim (insert_not_input C H e input (eq ▸ trivial))
  | cons edge es ih =>
      obtain ⟨w, op, target, source, tail⟩ := operationTrace_cons_iff.mp trace
      by_cases input : v.IsInput
      · cases v with
        | input j => exact .input j
        | internal => contradiction
        | output => contradiction
      · obtain ⟨f, ft⟩ := ((H e).target_coverage v).mpr input
        have inserted : insert C H e v ∈ (C.expand H).target ⟨e,f⟩ := List.mem_map_of_mem ft
        have same : edge = ⟨e,f⟩ := (C.expand H).target_unique target inserted
        subst edge
        obtain ⟨x, hx, xe⟩ := List.mem_map.mp source
        obtain ⟨j, fs, inside⟩ := ih (v := x) (xe.symm ▸ tail)
        exact ⟨j, f :: fs, .cons op ft hx inside⟩

/-- A one-way filling excludes reachability of any term-typed host target
of the edge it replaces, even when other edges are replaced simultaneously. -/
theorem oneWay_target (e : C.Edge) (one : OneWay (H e)) {v : C.Vertex}
    (term : C.vertexLabel v = .term) (target : v ∈ C.target e) :
    ¬ OperationReachable (C.expand H) (host C H v) := by
  obtain ⟨j, rfl⟩ := (C.mem_target_iff_port e v).mp target
  intro root
  have reach := extract C H e (v := .output j) root
  have typed : (H e).vertexLabel (.output j) = .term := (C.targetPort_label e j).symm.trans term
  exact (oneWay_iff.mp one) j typed reach

variable (K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- Each original edge is either retained on both sides, or has a one-way
filling on at least one side. The chosen side may vary from edge to edge. -/
def OutputClosedPair : Prop := ∀ e : C.Edge,
  (Nonempty (CorollaCopy C H e) ∧ Nonempty (CorollaCopy C K e)) ∨
    OneWay (H e) ∨ OneWay (K e)

/-- Synchronous backwards reasoning at one original edge. A target reachable
on both sides rules out either one-way case; retained copies then give
operation labels and reachability of every original source on both sides. -/
theorem predecessor (closed : OutputClosedPair C H K) {e : C.Edge} {v : C.Vertex}
    (term : C.vertexLabel v = .term) (target : v ∈ C.target e)
    (left : OperationReachable (C.expand H) (host C H v))
    (right : OperationReachable (C.expand K) (host C K v)) :
    IsOperation ops d (C.edgeLabel e) ∧ ∀ w ∈ C.source e,
      C.vertexLabel w = .term ∧ OperationReachable (C.expand H) (host C H w) ∧
        OperationReachable (C.expand K) (host C K w) := by
  rcases closed e with ⟨⟨l⟩,⟨r⟩⟩ | one | one
  · have lt := copy_target C H l target
    have rt := copy_target C K r target
    have op : IsOperation ops d (C.edgeLabel e) := by
      have h := left.incoming_operation lt
      change IsOperation ops d ((H e).edgeLabel l.edge) at h
      rwa [l.label] at h
    exact ⟨op, fun w mem => ⟨operation_source_term op mem,
      (left.predecessor lt (copy_source C H l mem)).2,
      (right.predecessor rt (copy_source C K r mem)).2⟩⟩
  · exact False.elim (oneWay_target C H e one term target left)
  · exact False.elim (oneWay_target C K e one term target right)

/-- Every edge of a host path to a term vertex reachable on both sides is
an operation, and its sources are term vertices reachable on both sides. -/
theorem path_operations (closed : OutputClosedPair C H K)
    {es : List C.Edge} (path : C.Path es) {last : C.Edge}
    (endEdge : es.getLast? = some last) {v : C.Vertex} (target : v ∈ C.target last)
    (term : C.vertexLabel v = .term)
    (left : OperationReachable (C.expand H) (host C H v))
    (right : OperationReachable (C.expand K) (host C K v)) :
    ∀ e ∈ es, IsOperation ops d (C.edgeLabel e) ∧ ∀ w ∈ C.source e,
      C.vertexLabel w = .term ∧ OperationReachable (C.expand H) (host C H w) ∧
        OperationReachable (C.expand K) (host C K w) := by
  induction path with
  | single e =>
      have same : e = last := by simpa using endEdge
      subst last
      intro f mem
      have same := List.mem_singleton.mp mem
      subst f
      exact predecessor C H K closed term target left right
  | @cons e f es adjacent path ih =>
      have rest := ih (by simpa using endEdge)
      obtain ⟨w, we, wf⟩ := adjacent
      obtain ⟨typed, l, r⟩ := (rest f (by simp)).2 w wf
      intro g mem
      cases List.mem_cons.mp mem with
      | inl eq => subst g; exact predecessor C H K closed typed we l r
      | inr mem => exact rest g mem

end ExpansionPaths
end Hypernets.Linear
