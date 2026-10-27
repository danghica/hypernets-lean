import Hypernets.Copying.CopyCoherenceExamples

/-! Rootedness and operation reachability for the unchanged copying search relation. -/
namespace Hypernets.Copying.Search
open Graph

/-- Search rootedness uses the state's own graph and a specified external input. -/
def RootedFrom {d I O} (G : Hypernet d I O) (i : Fin I.length) (p : Position G) : Prop :=
  ∃ n, (machine G).Steps n (.search,.input i) p

/-- Operation-only reachability is an invariant of search, not a replacement for rootedness. -/
inductive OperationReachable {d I O} (G : Hypernet d I O) : G.Vertex → Prop where
  | input (i : Fin I.length) : OperationReachable G (.input i)
  | argument {e o root v} (label : G.edgeLabel e = primitiveLabel d (.operation o))
      (source : G.source e = [root]) (parent : OperationReachable G root)
      (member : v ∈ G.target e) : OperationReachable G v

/-- Any operation consumes exactly its given singleton source. -/
theorem operation_source {d I O} {G : Hypernet d I O} {e o v}
    (label : G.edgeLabel e = primitiveLabel d (.operation o)) (mem : v ∈ G.source e) :
    G.source e = [v] := by
  have len : (G.source e).length = 1 := by rw [G.source_length,label,primitive_input]; rfl
  obtain ⟨w,hw⟩ := List.length_eq_one_iff.mp len
  have eq : v = w := by simpa [hw] using mem
  simpa [eq] using hw

/-- Incoming-edge uniqueness recovers the operation parent of a reachable argument. -/
theorem OperationReachable.parent {d I O} {G : Hypernet d I O} {v e root}
    (reach : OperationReachable G v) (source : G.source e = [root]) (mem : v ∈ G.target e) :
    OperationReachable G root := by
  cases reach with
  | input i => exact False.elim (G.target_not_input mem trivial)
  | argument label src parent member =>
    have eq := G.target_unique mem member
    have same := (List.cons.inj (source.symm.trans ((congrArg G.source eq).trans src))).1
    exact same ▸ parent

/-- A non-operation producer blocks operation reachability, including in cyclic hosts. -/
theorem OperationReachable.not_nonoperation_target {d I O} {G : Hypernet d I O} {v e}
    (reach : OperationReachable G v)
    (blocked : ∀ o, G.edgeLabel e ≠ primitiveLabel d (.operation o)) (mem : v ∈ G.target e) : False := by
  cases reach with
  | input i => exact G.target_not_input mem trivial
  | argument label src parent member =>
    exact blocked _ ((congrArg G.edgeLabel (G.target_unique mem member)).trans label)

/-- Every search interaction preserves operation-only reachability of its token. -/
theorem step_reachable {d I O} {G : Hypernet d I O} {s t : Position G}
    (step : Step G s t) (reach : OperationReachable G s.2) : OperationReachable G t.2 := by
  cases step with
  | search e p v t label src result =>
    cases p with
    | operation o =>
      have source := operation_source label src
      simp only [enter] at result
      split at result
      · have eq := (Option.some.inj result).symm; subst t; exact reach
      · obtain ⟨w,mem,eq⟩ := Option.map_eq_some_iff.mp result
        subst t
        exact .argument label source reach (List.mem_of_getElem? mem)
    | contraction s => cases s <;> simp only [enter] at result
                       · cases result; exact reach
                       · cases result
    | instanceEdge => cases result; exact reach
    | weakening s => cases result
    | store => cases result
    | hole h => cases result
    | focus m => cases result
  | backtrack e o root v i t label src bound arg result =>
    have parent := reach.parent src (List.mem_of_getElem? arg)
    simp only [resume] at result
    split at result
    · obtain ⟨w,mem,eq⟩ := Option.map_eq_some_iff.mp result
      subst t
      exact .argument label src parent (List.mem_of_getElem? mem)
    · cases result; exact parent

theorem run_reachable {d I O} {G : Hypernet d I O} {n s t}
    (run : (machine G).Steps n s t) (reach : OperationReachable G s.2) : OperationReachable G t.2 := by
  induction run with
  | zero => exact reach
  | cons step run ih => exact ih (step_reachable step reach)

theorem rooted_reachable {d I O} {G : Hypernet d I O} {i p} (root : RootedFrom G i p) :
    OperationReachable G p.2 := by
  obtain ⟨n,run⟩ := root
  exact run_reachable run (.input i)

theorem rooted_initial {d I O} (G : Hypernet d I O) (i : Fin I.length) : RootedFrom G i (.search,.input i) :=
  ⟨0,.zero _⟩

theorem rooted_step {d I O} {G : Hypernet d I O} {i s t}
    (root : RootedFrom G i s) (step : Step G s t) : RootedFrom G i t := by
  obtain ⟨n,run⟩ := root
  exact ⟨n+1,run.append (.cons step (.zero _))⟩

theorem rooted_iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) (i : Fin I.length) (p : Position G) :
    RootedFrom H i (p.1,Port.map f.vertices.toFun p.2) ↔ RootedFrom G i p := by
  let t := ofBoundaryIso (BoundaryIso.ofDeepIso f)
  exact exists_congr (fun n => t.machine_steps_iff n (.search,.input i) p)
end Hypernets.Copying.Search

namespace Hypernets.Copying.Combined
/-- The paper's rooted predicate on closed coordinate states, defined by search alone. -/
def Rooted {d} (s : State d [.term] []) : Prop := Search.RootedFrom s.1 0 s.2

def UnboundedRooted (s : UnboundedState) : Prop := Rooted s.2

theorem rooted_iso {d} {s t : State d [.term] []} (f : StateIso s t) : Rooted s ↔ Rooted t := by
  have eq : (s.2.1,Graph.Port.map f.graph.vertices.toFun s.2.2) = t.2 := Prod.ext f.mode f.vertex
  exact ((Search.rooted_iso f.graph 0 s.2).symm).trans (by rw [eq];rfl)

theorem initial_rooted (P : ClosedProgram) : UnboundedRooted (execution.initial P) :=
  Search.rooted_initial P.graph 0

theorem represents_rooted {s t : UnboundedState} (f : Represents s t) : UnboundedRooted s ↔ UnboundedRooted t := by
  cases f with | lift f => exact rooted_iso f
end Hypernets.Copying.Combined
