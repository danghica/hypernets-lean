import Hypernets.Graph.DepthInventory

/-! Padding embeds recursive state classes injectively. -/
namespace Hypernets.Linear.DepthPadding
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Lift carrier bijections when their local label relation is preserved. -/
def mapIso {n I O} {G H : Hypernet ops n I O}
    (labels : ∀ p q, LabelEquiv ops n p q → LabelEquiv ops (n+1) (label n p) (label n q))
    (f : DeepIso G H) : DeepIso (graph G) (graph H) where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := labels _ _ (f.edge_label e)
  source := f.source
  target := f.target

/-- Reflect carrier bijections when the local label relation is reflected. -/
def unmapIso {n I O} {G H : Hypernet ops n I O}
    (labels : ∀ p q, LabelEquiv ops (n+1) (label n p) (label n q) → LabelEquiv ops n p q)
    (f : DeepIso (graph G) (graph H)) : DeepIso G H where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := labels _ _ (f.edge_label e)
  source := f.source
  target := f.target

/-- Padding neither identifies distinct recursive labels nor separates equal ones. -/
theorem label_equiv_iff (n : Nat) (p q : (alphabet ops n).Symbol) :
    LabelEquiv ops (n+1) (label n p) (label n q) ↔ LabelEquiv ops n p q := by
  induction n with
  | zero =>
    cases p with | up p => cases q with | up q =>
      exact ⟨congrArg ULift.up,fun h => congrArg ULift.down h⟩
  | succ n ih =>
    cases p with
    | inl p => cases q with
      | inl q => rfl
      | inr q => rfl
    | inr p => cases q with
      | inl q => rfl
      | inr q =>
        constructor
        · intro h
          cases p with | mk pb pf p => cases q with | mk qb qf q =>
            cases h with
            | bodies f =>
              obtain ⟨f⟩ := f
              rw [← graph_eq_raise,← graph_eq_raise] at f
              exact .bodies ⟨unmapIso (fun p q h => (ih p q).mp h) f⟩
        · intro h
          cases h with
          | bodies f =>
            obtain ⟨f⟩ := f
            apply BoxRelated.bodies
            rw [← graph_eq_raise,← graph_eq_raise]
            exact ⟨mapIso (fun p q h => (ih p q).mpr h) f⟩

def deepIso {n I O} {G H : Hypernet ops n I O} (f : DeepIso G H) : DeepIso (graph G) (graph H) :=
  mapIso (fun p q h => (label_equiv_iff n p q).mpr h) f

def reflectIso {n I O} {G H : Hypernet ops n I O} (f : DeepIso (graph G) (graph H)) : DeepIso G H :=
  unmapIso (fun p q h => (label_equiv_iff n p q).mp h) f

/-- The distinguished focus is unchanged while inner names may still vary. -/
def stateIso {n} {s t : State ops n} (f : Focussed.DeepIso s.focussed t.focussed) :
    Focussed.DeepIso (state s).focussed (state t).focussed :=
  ⟨deepIso f.graph,f.mode,f.focus⟩

def reflectStateIso {n} {s t : State ops n}
    (f : Focussed.DeepIso (state s).focussed (state t).focussed) :
    Focussed.DeepIso s.focussed t.focussed := ⟨reflectIso f.graph,f.mode,f.focus⟩

/-- A well-defined embedding of recursive state classes into the next depth. -/
def stateClass {n} (s : DeepStateClass ops n) : DeepStateClass ops (n+1) :=
  Quotient.liftOn s (fun s => DeepStateClass.ofState (state s))
    (fun _ _ ⟨f⟩ => Quotient.sound ⟨stateIso f⟩)

theorem stateClass_injective {n} {s t : DeepStateClass ops n} (h : stateClass s = stateClass t) : s = t := by
  induction s,t using Quotient.inductionOn₂ with
  | h s t =>
    obtain ⟨f⟩ := Quotient.exact h
    exact Quotient.sound ⟨reflectStateIso f⟩

theorem class_initial_iff {n} (s : DeepStateClass ops n) :
    DeepStateClass.Initial (stateClass s) ↔ DeepStateClass.Initial s := by
  induction s using Quotient.inductionOn with | h s => exact state_initial_iff s

theorem class_final_iff {n} (s : DeepStateClass ops n) :
    DeepStateClass.Final (stateClass s) ↔ DeepStateClass.Final s := by
  induction s using Quotient.inductionOn with | h s => exact state_final_iff s
end Hypernets.Linear.DepthPadding
