import Hypernets.Graph.StateQuotient
import Hypernets.Graph.RecursiveIsoHoles

/-! Focused recursive isomorphisms allow independent renaming inside boxes. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Recursive label equivalence fixes each specified primitive symbol exactly. -/
theorem labelEquiv_primitive {d} {a b : (alphabet ops d).Symbol}
    (h : LabelEquiv ops d a b) (p : Primitive Op)
    (eq : a = primitiveLabel ops d p) : b = primitiveLabel ops d p := by
  subst a
  cases d with
  | zero => exact h.symm
  | succ d =>
      cases b with
      | inl b => exact congrArg Sum.inl h.symm
      | inr b => exact False.elim h

/-- Absence of focuses throughout a label is invariant under recursive renaming. -/
theorem labelEquiv_focusFree (ops : Operations Op) (d : Nat)
    {a b : (alphabet ops d).Symbol} (h : LabelEquiv ops d a b) :
    LabelFocusFree ops d a ↔ LabelFocusFree ops d b := by
  induction d with
  | zero => cases h; rfl
  | succ d ih =>
      cases a with
      | inl a => cases b with
        | inl b => cases h; rfl
        | inr b => exact False.elim h
      | inr a => cases b with
        | inl b => exact False.elim h
        | inr b =>
          cases h with
          | bodies related =>
              obtain ⟨f⟩ := related
              constructor
              · intro free e
                have he := (ih (f.edge_label (f.edges.invFun e))).mp (free _)
                simpa only [f.edges.right_inv] using he
              · intro free e
                exact (ih (f.edge_label e)).mpr (free _)

theorem DeepIso.focusFree_iff {d I O} {G H : Hypernet ops d I O} (a : DeepIso G H) :
    FocusFree G ↔ FocusFree H := by
  constructor
  · intro free e
    have h := (labelEquiv_focusFree ops d (a.edge_label (a.edges.invFun e))).mp (free _)
    simpa only [a.edges.right_inv] using h
  · intro free e
    exact (labelEquiv_focusFree ops d (a.edge_label e)).mpr (free _)

namespace Focussed

/-- A recursive graph isomorphism preserving the distinguished focus and mode. -/
structure DeepIso {d I O} {G H : Hypernet ops d I O} (f : Focussed G) (g : Focussed H) where
  graph : Linear.DeepIso G H
  mode : f.mode = g.mode
  focus : graph.edges.toFun f.edge = g.edge

namespace DeepIso
variable {d I O} {G H K : Hypernet ops d I O} {f : Focussed G} {g : Focussed H} {h : Focussed K}

def refl (f : Focussed G) : DeepIso f f := ⟨Linear.DeepIso.refl G, rfl, rfl⟩

def symm (a : DeepIso f g) : DeepIso g f where
  graph := Linear.DeepIso.symm a.graph
  mode := a.mode.symm
  focus := by
    change a.graph.edges.invFun g.edge = f.edge
    rw [← a.focus, a.graph.edges.left_inv]

def trans (a : DeepIso f g) (b : DeepIso g h) : DeepIso f h where
  graph := Linear.DeepIso.trans a.graph b.graph
  mode := a.mode.trans b.mode
  focus := by
    change b.graph.edges.toFun (a.graph.edges.toFun f.edge) = h.edge
    rw [a.focus, b.focus]

/-- Every literal-label focused isomorphism is a recursive one. -/
def ofIso (a : Iso f g) : DeepIso f g := ⟨Linear.DeepIso.ofIso a.graph, a.mode, a.focus⟩

theorem source (a : DeepIso f g) : Port.map a.graph.vertices.toFun f.source = g.source := by
  have eq := a.graph.source f.edge
  rw [f.source_eq, a.focus, g.source_eq] at eq
  exact (List.cons.inj eq).1

theorem target (a : DeepIso f g) : Port.map a.graph.vertices.toFun f.target = g.target := by
  have eq := a.graph.target f.edge
  rw [f.target_eq, a.focus, g.target_eq] at eq
  exact (List.cons.inj eq).1

theorem initial_iff (a : DeepIso f g) : f.Initial ↔ g.Initial := by
  have input := Port.map_isInput a.graph.vertices.toFun f.source
  rw [a.source] at input
  simp only [Initial, a.mode, input]

theorem final_iff (a : DeepIso f g) : f.Final ↔ g.Final := by
  have input := Port.map_isInput a.graph.vertices.toFun f.source
  rw [a.source] at input
  simp only [Final, a.mode, input]

end DeepIso
end Focussed
end Hypernets.Linear
