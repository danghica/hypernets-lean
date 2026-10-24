import Hypernets.Graph.ObservationExamples

/-! Depth padding of actual graphs and focussed states. Padding is representation,
not an execution step; outer carriers and incidence are unchanged. -/
namespace Hypernets.Linear.DepthPadding
open Graph
variable {Op : Type} {ops : Operations Op}

/-- The label map underlying the existing recursive increase of depth allowance. -/
def label : (n : Nat) → (alphabet ops n).Symbol → (alphabet ops (n+1)).Symbol
  | 0, p => .inl p.down
  | _+1, .inl p => .inl p
  | n+1, .inr b => .inr ⟨b.bound,b.free,raise ops n b.body⟩

theorem label_input (n : Nat) (p : (alphabet ops n).Symbol) :
    (alphabet ops (n+1)).signature.input (label n p) = (alphabet ops n).signature.input p := by
  cases n with
  | zero => rfl
  | succ n => cases p <;> rfl

theorem label_output (n : Nat) (p : (alphabet ops n).Symbol) :
    (alphabet ops (n+1)).signature.output (label n p) = (alphabet ops n).signature.output p := by
  cases n with
  | zero => rfl
  | succ n => cases p <;> rfl

/-- A uniform relabelling presentation, with definitionally unchanged carriers. -/
def graph {n I O} (G : Hypernet ops n I O) : Hypernet ops (n+1) I O :=
  G.relabel _ (label n) (label_input n) (label_output n)

theorem graph_eq_raise {n I O} (G : Hypernet ops n I O) : graph G = raise ops n G := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold graph raise
    congr 1
    funext p
    cases p <;> rfl

theorem label_primitive (n : Nat) (p : Primitive Op) :
    label n (primitiveLabel ops n p) = primitiveLabel ops (n+1) p := by cases n <;> rfl

theorem label_focus (n : Nat) (m : Focus) :
    label n (focusLabel ops n m) = focusLabel ops (n+1) m := by cases n <;> rfl

/-- Padding preserves and reflects absence of focuses, including nested bodies. -/
theorem label_free (n : Nat) (p : (alphabet ops n).Symbol) :
    LabelFocusFree ops (n+1) (label n p) ↔ LabelFocusFree ops n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases p with
    | inl p => rfl
    | inr b =>
      change (∀ e, LabelFocusFree ops (n+1) ((raise ops n b.body).edgeLabel e)) ↔ _
      rw [← graph_eq_raise]
      exact ⟨fun h e => (ih _).mp (h e),fun h e => (ih _).mpr (h e)⟩

theorem focusFree_iff {n I O} (G : Hypernet ops n I O) : FocusFree (graph G) ↔ FocusFree G :=
  ⟨fun h e => (label_free n _).mp (h e),fun h e => (label_free n _).mpr (h e)⟩

/-- The same selected edge and ports give a focus after padding. -/
def focussed {n I O} {G : Hypernet ops n I O} (f : Focussed G) : Focussed (graph G) where
  edge := f.edge
  mode := f.mode
  label := (congrArg (label n) f.label).trans (label_focus n f.mode)
  other_free e ne := (label_free n _).mpr (f.other_free e ne)
  source := f.source
  target := f.target
  source_eq := f.source_eq
  target_eq := f.target_eq
  self_acyclic := f.self_acyclic
  not_exposed := f.not_exposed

/-- Initial and final boundary observations are unchanged by padding. -/
theorem focussed_initial_iff {n I O} {G : Hypernet ops n I O} (f : Focussed G) :
    (focussed f).Initial ↔ f.Initial := Iff.rfl

theorem focussed_final_iff {n I O} {G : Hypernet ops n I O} (f : Focussed G) :
    (focussed f).Final ↔ f.Final := Iff.rfl
end Hypernets.Linear.DepthPadding
