import Hypernets.Copying.OneWay

/-! Correspondence of the copying one-way predicate with actual operation paths. -/
namespace Hypernets.Copying
open Graph

theorem isOperation_iff {d} (l : (alphabet d).Symbol) :
    IsOperation d l ↔ ∃ o, l = primitiveLabel d (.operation o) := by
  cases d with
  | zero =>
    cases l with
    | up p =>
      cases p <;> simp [IsOperation,primitiveLabel]
      all_goals first | exact ⟨_,rfl⟩ | intro x eq; cases eq
  | succ d =>
    cases l with
    | inl p =>
      cases p <;> simp [IsOperation,primitiveLabel]
      all_goals first | exact ⟨_,rfl⟩ | intro x eq; cases eq
    | inr b => simp [IsOperation,primitiveLabel]

namespace Search
/-- The inductive reachability invariant records exactly an operation-only path. -/
theorem operationReachable_iff {d I O} {G : Hypernet d I O} (v : G.Vertex) :
    OperationReachable G v ↔ ∃ i es, G.OperationTrace (IsOperation d) v es (.input i) := by
  constructor
  · intro reachable
    induction reachable with
    | input i => exact ⟨i,[],.nil _⟩
    | @argument e o root v label source parent member ih =>
      obtain ⟨i,es,path⟩ := ih
      exact ⟨i,e::es,.cons ((isOperation_iff _).mpr ⟨o,label⟩) member (by simp [source]) path⟩
  · rintro ⟨i,es,path⟩
    have recover {v z es} (path : G.OperationTrace (IsOperation d) v es z) :
        OperationReachable G z → OperationReachable G v := by
      induction path with
      | nil => exact id
      | cons op target source tail ih =>
        obtain ⟨o,label⟩ := (isOperation_iff _).mp op
        exact fun rooted => .argument label (operation_source label source) (ih rooted) target
    exact recover path (.input i)

/-- A nonempty operation path starts at a term input; other input sorts do not
silently strengthen the one-way predicate. -/
theorem operationTrace_input_term {d I O} {G : Hypernet d I O} {i v es}
    (path : G.OperationTrace (IsOperation d) v es (.input i)) (nonempty : es ≠ []) :
    G.vertexLabel (.input i) = .term := by
  have rootTerm {e} (op : IsOperation d (G.edgeLabel e)) {v} (mem : v ∈ G.source e) :
      G.vertexLabel v = .term := by
    obtain ⟨o,label⟩ := (isOperation_iff _).mp op
    have typed := List.mem_map_of_mem (f := G.vertexLabel) mem
    change G.vertexLabel v ∈ (G.source e).map (Port.label G.internalLabel) at typed
    rw [G.source_typed,label,primitive_input] at typed
    exact List.mem_singleton.mp typed
  induction es generalizing v with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
    cases path with
    | cons op target source tail =>
      cases es with
      | nil => cases tail; exact rootTerm op source
      | cons f fs => exact ih tail (by simp)
end Search

/-- The paper's term-input to term-output formulation, with forward edge order. -/
theorem oneWay_iff_paths {d I O} (G : Hypernet d I O) : OneWay G ↔
    ∀ (i : Fin I.length) (j : Fin O.length),
      G.vertexLabel (.input i) = .term → G.vertexLabel (.output j) = .term →
      ∀ es, ¬ G.OperationPath (IsOperation d) (.input i) es (.output j) := by
  constructor
  · intro one i j _ term es path
    exact one j term ((Search.operationReachable_iff _).mpr ⟨i,es.reverse,path⟩)
  · intro paths j term reach
    obtain ⟨i,es,path⟩ := (Search.operationReachable_iff _).mp reach
    have nonempty : es ≠ [] := by intro eq; subst es; cases path
    exact paths i j (Search.operationTrace_input_term path nonempty) term es.reverse
      (by simpa [Net.OperationPath] using path)
end Hypernets.Copying
