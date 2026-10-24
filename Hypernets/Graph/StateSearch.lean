import Hypernets.Graph.FocusRoundTrip

/-! A search relation on arbitrary explicit states, via general erasure and
reinsertion modulo focus-preserving isomorphism. Local rewrite adequacy remains open. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

namespace Focussed

/-- A graph isomorphism that identifies the distinguished focus and its mode. -/
structure Iso {d I O} {G H : Hypernet ops d I O} (f : Focussed G) (g : Focussed H) where
  graph : Net.Iso G H
  mode : f.mode = g.mode
  focus : graph.edges.toFun f.edge = g.edge

namespace Iso
variable {d I O} {G H K : Hypernet ops d I O} {f : Focussed G} {g : Focussed H} {h : Focussed K}

def refl (f : Focussed G) : Iso f f := ⟨Net.Iso.refl G, rfl, rfl⟩

def symm (a : Iso f g) : Iso g f where
  graph := a.graph.symm
  mode := a.mode.symm
  focus := by
    change a.graph.edges.invFun g.edge = f.edge
    rw [← a.focus, a.graph.edges.left_inv]

def trans (a : Iso f g) (b : Iso g h) : Iso f h where
  graph := a.graph.trans b.graph
  mode := a.mode.trans b.mode
  focus := by
    change b.graph.edges.toFun (a.graph.edges.toFun f.edge) = h.edge
    rw [a.focus, b.focus]

theorem source (a : Iso f g) : Port.map a.graph.vertices.toFun f.source = g.source := by
  have eq := a.graph.source f.edge
  rw [f.source_eq, a.focus, g.source_eq] at eq
  exact (List.cons.inj eq).1

theorem target (a : Iso f g) : Port.map a.graph.vertices.toFun f.target = g.target := by
  have eq := a.graph.target f.edge
  rw [f.target_eq, a.focus, g.target_eq] at eq
  exact (List.cons.inj eq).1

theorem initial_iff (a : Iso f g) : f.Initial ↔ g.Initial := by
  have input := Port.map_isInput a.graph.vertices.toFun f.source
  rw [a.source] at input
  simp only [Initial, a.mode, input]

theorem final_iff (a : Iso f g) : f.Final ↔ g.Final := by
  have input := Port.map_isInput a.graph.vertices.toFun f.source
  rw [a.source] at input
  simp only [Final, a.mode, input]

end Iso
end Focussed

namespace State
variable {d : Nat}

/-- Coordinates obtained from an arbitrary state's certified general erasure. -/
noncomputable def coordinate (s : State ops d) : TypedPosition s.focussed.underlying :=
  ⟨(s.focussed.mode, FocusErasure.position s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec),
    FocusErasure.position_term s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec⟩

/-- Reconstructing an arbitrary state from its extracted coordinate preserves
its graph, distinguished focus, and mode up to explicit isomorphism. -/
noncomputable def recover (s : State ops d) :
    Focussed.Iso ((coordinate s).realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)).focussed s.focussed where
  graph := s.focussed.underlying_reinsert_iso
  mode := rfl
  focus := rfl

theorem coordinate_boundary (s : State ops d) :
    ((coordinate s).val.1 = .search ∧ (coordinate s).val.2.IsInput ↔ s.focussed.Initial) ∧
    ((coordinate s).val.1 = .backtrack ∧ (coordinate s).val.2.IsInput ↔ s.focussed.Final) := by
  have b := (coordinate s).realize_boundary s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free)
  exact ⟨b.1.symm.trans (recover s).initial_iff, b.2.symm.trans (recover s).final_iff⟩

/-- Erasure-based search on actual states. Targets may use arbitrary vertex and
edge names, provided they are focus-preservingly isomorphic to the realized result.
Equivalence to the paper's contextual local-rewrite definition remains to prove. -/
def Search (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  ∃ q : TypedPosition s.focussed.underlying,
    SearchStep s.focussed.underlying kind (coordinate s).val q.val ∧
    Nonempty (Focussed.Iso (q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)).focussed t.focussed)

/-- Every coordinate successor yields an actual state successor. -/
theorem search_realize (kind : Op → OperationKind) (s : State ops d)
    (q : TypedPosition s.focussed.underlying)
    (step : SearchStep s.focussed.underlying kind (coordinate s).val q.val) :
    Search kind s (q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)) :=
  ⟨q, step, ⟨Focussed.Iso.refl _⟩⟩

/-- Renaming a successor while preserving its focus preserves the search step. -/
theorem search_target_iso {kind : Op → OperationKind} {s t u : State ops d}
    (step : Search kind s t) (iso : Focussed.Iso t.focussed u.focussed) : Search kind s u := by
  obtain ⟨q, hq, ⟨qt⟩⟩ := step
  exact ⟨q, hq, ⟨qt.trans iso⟩⟩

/-- Search is deterministic modulo focus-preserving graph isomorphism. -/
theorem search_deterministic {kind : Op → OperationKind} {s t u : State ops d}
    (left : Search kind s t) (right : Search kind s u) : Nonempty (Focussed.Iso t.focussed u.focussed) := by
  obtain ⟨q, hq, ⟨qt⟩⟩ := left
  obtain ⟨r, hr, ⟨ru⟩⟩ := right
  have eq : q = r := Subtype.ext (SearchStep.deterministic hq hr)
  subst r
  exact ⟨qt.symm.trans ru⟩

/-- An explicit final state has no erasure-based search transition. -/
theorem final_no_search {kind : Op → OperationKind} {s t : State ops d}
    (final : s.focussed.Final) : ¬ Search kind s t := by
  rintro ⟨q, step, _⟩
  have b := (coordinate_boundary s).2.mpr final
  have eq : (coordinate s).val = (.backtrack, (coordinate s).val.2) := Prod.ext b.1 rfl
  rw [eq] at step
  exact SearchStep.final_no_step b.2 step

/-- No erasure-based search transition ends in an explicit initial state. -/
theorem no_search_initial {kind : Op → OperationKind} {s t : State ops d}
    (initial : t.focussed.Initial) : ¬ Search kind s t := by
  rintro ⟨q, step, ⟨iso⟩⟩
  have h := iso.initial_iff.mpr initial
  have b := (q.realize_boundary s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free)).1.mp h
  have eq : q.val = (.search, q.val.2) := Prod.ext b.1 rfl
  rw [eq] at step
  exact SearchStep.no_initial_target b.2 step

end State
end Hypernets.Linear
