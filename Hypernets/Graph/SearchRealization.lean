import Hypernets.Graph.FocusInsertion

/-! Typed search positions realized as actual hole-free focussed states.
This supplies insertion and incidence recovery; adequacy for arbitrary focussed
states and the local contextual rewrite presentation remains open. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

namespace SearchOperation
variable {d I O} {G : Hypernet ops d I O}

/-- The singleton source of an operation is a term vertex. -/
theorem source_term (a : SearchOperation G) : G.vertexLabel a.source = .term := by
  have typed := G.source_typed a.edge
  rw [a.source_eq, a.label] at typed
  cases d <;> simpa [primitiveLabel, alphabet, baseAlphabet, nextAlphabet, primitiveSignature,
    Net.vertexLabel] using typed

/-- The argument prefix consists exactly of term vertices, never thunks. -/
theorem arguments_typed (a : SearchOperation G) :
    a.arguments.map G.vertexLabel = List.replicate (ops.arguments a.operation) .term := by
  have typed := G.target_typed a.edge
  rw [a.target_eq, List.map_append, a.label] at typed
  have output : (alphabet ops d).signature.output (primitiveLabel ops d (.operation a.operation)) =
      List.replicate (ops.arguments a.operation) .term ++ (ops.binders a.operation).map Wire.thunk := by
    cases d <;> rfl
  rw [output] at typed
  change a.arguments.map G.vertexLabel ++ a.thunks.map G.vertexLabel = _ at typed
  have len : (a.arguments.map G.vertexLabel).length = (List.replicate (ops.arguments a.operation) Wire.term).length := by
    simp [a.arity]
  have eq := congrArg (List.take (a.arguments.map G.vertexLabel).length) typed
  simp only [List.take_left] at eq
  rw [len, List.take_left] at eq
  exact eq

theorem argument_term (a : SearchOperation G) {v : G.Vertex} (mem : v ∈ a.arguments) :
    G.vertexLabel v = .term := by
  have h := List.mem_map_of_mem (f := G.vertexLabel) mem
  rw [a.arguments_typed] at h
  exact (List.mem_replicate.mp h).2

end SearchOperation

/-- Search preserves the term-vertex typing required to insert a focus. -/
theorem SearchStep.preserves_term {d I O} {G : Hypernet ops d I O}
    {kind : Op → OperationKind} {p q : SearchPosition G} (step : SearchStep G kind p q)
    (typed : G.vertexLabel p.2 = .term) : G.vertexLabel q.2 = .term := by
  cases step with
  | trigger e v label source => exact typed
  | enter a =>
      simp only [SearchOperation.enter]
      split
      next h => exact a.source_term
      next v rest h => exact a.argument_term (by simp [h])
  | resume a i v arg =>
      simp only [SearchOperation.resume]
      split
      next v next => exact a.argument_term (List.mem_of_getElem? next)
      next absent => exact a.source_term

/-- Coordinates at term vertices of a closed-interface underlying graph. -/
abbrev TypedPosition {d} (G : Hypernet ops d [.term] []) :=
  {p : SearchPosition G // G.vertexLabel p.2 = .term}

namespace TypedPosition
variable {d} {G : Hypernet ops d [.term] []}

/-- A closed-interface graph has no output vertices. -/
theorem not_output (p : TypedPosition G) : ¬ p.val.2.IsOutput := by
  cases p.val.2 with
  | internal v => exact id
  | input i => exact id
  | output i => exact Fin.elim0 i

/-- Insert the coordinate's mode at its term vertex, obtaining an actual state. -/
noncomputable def realize (p : TypedPosition G) (focusFree : FocusFree G)
    (holeFree : HoleFree G) : State ops d where
  graph := FocusInsertion.insert G p.val.2 p.property p.not_output p.val.1
  focussed := FocusInsertion.focussed G p.val.2 p.property p.not_output p.val.1 focusFree
  hole_free := FocusInsertion.holeFree G p.val.2 p.property p.not_output p.val.1 holeFree

/-- An initial coordinate is search at the sole input. -/
def initial (G : Hypernet ops d [.term] []) : TypedPosition G :=
  ⟨(.search, .input 0), rfl⟩

/-- Initial focus attachment now constructs a state, not an interface assumption. -/
theorem initial_realize (focusFree : FocusFree G) (holeFree : HoleFree G) :
    ((initial G).realize focusFree holeFree).focussed.Initial := ⟨rfl, trivial⟩

/-- Boundary observations of a realized state coincide with its coordinates. -/
theorem realize_boundary (p : TypedPosition G) (focusFree : FocusFree G) (holeFree : HoleFree G) :
    ((p.realize focusFree holeFree).focussed.Initial ↔ p.val.1 = .search ∧ p.val.2.IsInput) ∧
    ((p.realize focusFree holeFree).focussed.Final ↔ p.val.1 = .backtrack ∧ p.val.2.IsInput) :=
  FocusInsertion.boundary_iff G p.val.2 p.property p.not_output p.val.1 focusFree

/-- Lift a search result to a typed coordinate, using the proved preservation law. -/
def advance (p : TypedPosition G) {kind : Op → OperationKind} {q : SearchPosition G}
    (step : SearchStep G kind p.val q) : TypedPosition G :=
  ⟨q, step.preserves_term p.property⟩

/-- Every typed coordinate search step has genuine focussed state endpoints;
contracting either new focus recovers every original incidence list. -/
theorem step_realizes (p : TypedPosition G) {kind : Op → OperationKind} {q : SearchPosition G}
    (step : SearchStep G kind p.val q) (focusFree : FocusFree G) (holeFree : HoleFree G) :
    let s := p.realize focusFree holeFree;
    let t := (p.advance step).realize focusFree holeFree;

      s.focussed.mode = p.val.1 ∧ t.focussed.mode = q.1 ∧
      (∀ e : G.Edge,
        (s.graph.source (.inl e)).map (FocusInsertion.collapse G p.val.2) = G.source e ∧
        (s.graph.target (.inl e)).map (FocusInsertion.collapse G p.val.2) = G.target e) ∧
      (∀ e : G.Edge,
        (t.graph.source (.inl e)).map (FocusInsertion.collapse G q.2) = G.source e ∧
        (t.graph.target (.inl e)).map (FocusInsertion.collapse G q.2) = G.target e) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro e
    exact ⟨FocusInsertion.collapse_sources G p.val.2 p.property p.not_output p.val.1 e,
      FocusInsertion.collapse_targets G p.val.2 p.property p.not_output p.val.1 e⟩
  · intro e
    exact ⟨FocusInsertion.collapse_sources G q.2 (p.advance step).property (p.advance step).not_output q.1 e,
      FocusInsertion.collapse_targets G q.2 (p.advance step).property (p.advance step).not_output q.1 e⟩

end TypedPosition
end Hypernets.Linear
