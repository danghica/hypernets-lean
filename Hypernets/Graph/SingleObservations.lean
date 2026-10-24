import Hypernets.Graph.ConcreteObservations

/-! Ordinary single-fragment contextual refinement as a special case. -/
namespace Hypernets.Linear.ConcreteObservations
open ObservationFillings
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

/-- The interface containing one typed hole at a specified nesting depth. -/
def singleSlot (n : Nat) (h : Hole) : Slots := fun m k => m = n ∧ k = h

/-- Regard an arbitrary graph as a vector with precisely one declared slot. -/
def singleFragment {n : Nat} (h : Hole) (G : Hypernet ops n h.input h.output) :
    Fragments (ops := ops) (singleSlot n h) := by
  intro m k w
  obtain ⟨rfl,rfl⟩ := w
  exact G

/-- Single-vector relatedness is exactly the original pre-template relation. -/
theorem single_related_iff (T : LayeredPreTemplate ops) {n : Nat} (h : Hole)
    (G H : Hypernet ops n h.input h.output) :
    Related T (singleFragment h G) (singleFragment h H) ↔ (T n).Rel G H := by
  constructor
  · intro rel
    exact rel n h ⟨rfl,rfl⟩
  · intro rel m k w
    obtain ⟨rfl,rfl⟩ := w
    exact rel

variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (B : Behaviour ops d kind) (allowed : IsoClosedContexts Allowed)
    (closed : (T d).OutputClosed) (refocusing : RefocusingStates kind B.step)

include allowed closed refocusing in
/-- Forward sufficiency for arbitrary related graphs, not only fragment vectors. -/
theorem single_sufficiency {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : ClassSafety.InputSafe T Allowed B Q P) (robust : ClassSafety.Robust T Allowed B Q P R)
    {n : Nat} (h : Hole) {G H : Hypernet ops n h.input h.output} (rel : (T n).Rel G H) :
    (observations Allowed).Refines (UAMClasses.machine B) Q (singleFragment h G) (singleFragment h H) :=
  sufficiency T Allowed B allowed closed refocusing invariant det reasonable safe robust
    ((single_related_iff T h G H).mpr rel)

include allowed closed refocusing in
/-- Converse sufficiency for arbitrary related graphs with the original cost orientation. -/
theorem single_sufficiency_converse {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : ClassSafety.InputSafe T Allowed B Q.converse P)
    (robust : ClassSafety.ConverseRobust T Allowed B Q P R)
    {n : Nat} (h : Hole) {G H : Hypernet ops n h.input h.output} (rel : (T n).Rel G H) :
    (observations Allowed).Refines (UAMClasses.machine B) Q (singleFragment h H) (singleFragment h G) :=
  sufficiency_converse T Allowed B allowed closed refocusing invariant det reasonable safe robust
    ((single_related_iff T h G H).mpr rel)
end Hypernets.Linear.ConcreteObservations
