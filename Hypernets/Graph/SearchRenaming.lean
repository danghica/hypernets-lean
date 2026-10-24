import Hypernets.Graph.InsertionRoundTrip

/-! The search rules and typed coordinates are invariant under literal-label
isomorphisms of their underlying graphs. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    {G H : Hypernet ops d I O}

/-- Isomorphisms preserve the wire label of every port, including boundaries. -/
theorem iso_vertexLabel (a : Net.Iso G H) (v : G.Vertex) :
    H.vertexLabel (Port.map a.vertices.toFun v) = G.vertexLabel v := by
  cases v with
  | internal v => exact a.internal_label v
  | input i => rfl
  | output i => rfl

namespace SearchOperation

/-- Transport the entire ordered operation view through a graph isomorphism. -/
def rename (a : Net.Iso G H) (o : SearchOperation G) : SearchOperation H where
  edge := a.edges.toFun o.edge
  operation := o.operation
  label := (a.edge_label o.edge).trans o.label
  source := Port.map a.vertices.toFun o.source
  arguments := o.arguments.map (Port.map a.vertices.toFun)
  thunks := o.thunks.map (Port.map a.vertices.toFun)
  source_eq := by rw [← a.source, o.source_eq]; rfl
  target_eq := by rw [← a.target, o.target_eq, List.map_append]
  arity := by simpa using o.arity

theorem rename_enter (a : Net.Iso G H) (o : SearchOperation G) (kind : Op → OperationKind) :
    (o.rename a).enter kind = (o.enter kind).map id (Port.map a.vertices.toFun) := by
  simp only [enter, rename]
  cases o.arguments <;> rfl

theorem rename_resume (a : Net.Iso G H) (o : SearchOperation G) (kind : Op → OperationKind) (i : Nat) :
    (o.rename a).resume kind i = (o.resume kind i).map id (Port.map a.vertices.toFun) := by
  simp only [resume, rename, List.getElem?_map]
  cases o.arguments[i+1]? <;> rfl

end SearchOperation

namespace SearchStep

/-- Every one of the five coordinate rules commutes with renaming. -/
theorem rename (a : Net.Iso G H) {kind : Op → OperationKind} {p q : SearchPosition G}
    (step : SearchStep G kind p q) :
    SearchStep H kind (p.map id (Port.map a.vertices.toFun))
      (q.map id (Port.map a.vertices.toFun)) := by
  cases step with
  | trigger e v label source =>
      apply trigger (a.edges.toFun e)
      · exact (a.edge_label e).trans label
      · rw [← a.source, source]; rfl
  | enter o =>
      rw [← o.rename_enter a kind]
      exact enter (o.rename a)
  | resume o i v arg =>
      rw [← o.rename_resume a kind]
      apply resume (o.rename a) i
      simp [SearchOperation.rename, List.getElem?_map, arg]

/-- Transport both forwards and backwards: renaming creates no search steps. -/
theorem rename_iff (a : Net.Iso G H) {kind : Op → OperationKind} {p q : SearchPosition G} :
    SearchStep H kind (p.map id (Port.map a.vertices.toFun))
      (q.map id (Port.map a.vertices.toFun)) ↔ SearchStep G kind p q := by
  constructor
  · intro step
    have h := step.rename a.symm
    have inv (x : SearchPosition G) :
        (x.map id (Port.map a.vertices.toFun)).map id (Port.map a.symm.vertices.toFun) = x := by
      rcases x with ⟨m, v⟩
      apply Prod.ext
      · rfl
      exact (Port.bijection a.vertices).left_inv v
    simpa only [inv] using h
  · exact rename a

end SearchStep

namespace TypedPosition
variable {G H : Hypernet ops d [.term] []}

/-- Carry a term-typed coordinate through an isomorphism. -/
def rename (a : Net.Iso G H) (p : TypedPosition G) : TypedPosition H :=
  ⟨p.val.map id (Port.map a.vertices.toFun), (iso_vertexLabel a p.val.2).trans p.property⟩

/-- Typed coordinate transport has the inverse supplied by the inverse graph map. -/
theorem rename_symm (a : Net.Iso G H) (p : TypedPosition G) :
    (p.rename a).rename a.symm = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  exact (Port.bijection a.vertices).left_inv p.val.2

end TypedPosition
end Hypernets.Linear
