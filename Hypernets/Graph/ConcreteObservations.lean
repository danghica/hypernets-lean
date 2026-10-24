import Hypernets.Graph.ObservationFillings

/-! Concrete observations, initial lifting, and both contextual sufficiency clauses. -/
namespace Hypernets.Linear.ConcreteObservations
open Graph ObservationFillings
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

/-- An independently specified focus-free unique-hole context, whose original
holes belong to the interface. No template or paired filling is a field. -/
structure ObservationContext (slots : Slots) where
  net : Context ops d [.term] []
  free : FocusFree net.val
  covers : Covers slots net.val

/-- Contextual observations are initial classes of independently substituted
closed results. Neither membership nor observation mentions the template. -/
noncomputable def observations (Allowed : Hypernet ops d [.term] [] → Prop) :
    Observations (DeepStateClass ops d) Slots (Fragments (ops := ops))
      (ObservationContext (ops := ops) (d := d)) where
  allowed c := Allowed c.net.val
  observe c a s := InitialObservations.Observe (fill a c.net.val c.covers) s

variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (B : Behaviour ops d kind) (allowed : IsoClosedContexts Allowed)
    (closed : (T d).OutputClosed) (refocusing : RefocusingStates kind B.step)

/-- Proposition 38's concrete initial lifting obligation: independently given
observations of related vectors construct an allowed remote rooted specimen. -/
theorem initial_lifting {slots : Slots} {a b : Fragments (ops := ops) slots}
    (rel : Related T a b) (c : ObservationContext (ops := ops) (d := d) slots)
    {s t : DeepStateClass ops d} (hc : (observations Allowed).allowed c)
    (hs : (observations Allowed).observe c a s) (ht : (observations Allowed).observe c b t) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).Lifting s t := by
  have hs0 := hs
  have ht0 := ht
  obtain ⟨lf,lh,_⟩ := hs
  obtain ⟨rf,rh,_⟩ := ht
  exact InitialObservations.lifting c.net c.free _ _ (paired_edges T rel c.net.val c.covers)
    hc allowed (by simpa only [fill] using lh) (by simpa only [fill] using rh)
    B closed refocusing (by simpa only [observations,fill] using hs0)
    (by simpa only [observations,fill] using ht0)

include allowed closed refocusing in
/-- Concrete forward contextual sufficiency, with no initial-lifting premise. -/
theorem sufficiency {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : ClassSafety.InputSafe T Allowed B Q P) (robust : ClassSafety.Robust T Allowed B Q P R)
    {slots : Slots} {a b : Fragments (ops := ops) slots} (rel : Related T a b) :
    (observations Allowed).Refines (UAMClasses.machine B) Q a b :=
  (ClassSpecimens.system T Allowed B allowed closed refocusing).contextual_sufficiency
    (observations Allowed) (Related T)
    (fun {_ _ _} rel c {_ _} hc hs ht => initial_lifting T Allowed B allowed closed refocusing rel c hc hs ht)
    (fun {_ _ _} l r => UAMClasses.deterministic B invariant det l r) reasonable
    (ClassSafety.inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (ClassSafety.robust_bridge T Allowed B allowed closed refocusing robust) rel

include allowed closed refocusing in
/-- Concrete converse contextual sufficiency, retaining converse costs in safety. -/
theorem sufficiency_converse {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : ClassSafety.InputSafe T Allowed B Q.converse P)
    (robust : ClassSafety.ConverseRobust T Allowed B Q P R)
    {slots : Slots} {a b : Fragments (ops := ops) slots} (rel : Related T a b) :
    (observations Allowed).Refines (UAMClasses.machine B) Q b a :=
  (ClassSpecimens.system T Allowed B allowed closed refocusing).contextual_sufficiency_converse
    (observations Allowed) (Related T)
    (fun {_ _ _} rel c {_ _} hc hs ht => initial_lifting T Allowed B allowed closed refocusing rel c hc hs ht)
    (fun {_ _ _} l r => UAMClasses.deterministic B invariant det l r) reasonable
    (ClassSafety.inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (ClassSafety.converseRobust_bridge T Allowed B allowed closed refocusing robust) rel

include allowed closed refocusing in
/-- Both clauses combined for arbitrary allowed contexts and related fragment vectors. -/
theorem equivalence {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : ClassSafety.InputSafe T Allowed B Q P) (safeConverse : ClassSafety.InputSafe T Allowed B Q.converse P)
    (robust : ClassSafety.Robust T Allowed B Q P R) (robustConverse : ClassSafety.ConverseRobust T Allowed B Q P R)
    {slots : Slots} {a b : Fragments (ops := ops) slots} (rel : Related T a b) :
    (observations Allowed).Equiv (UAMClasses.machine B) Q a b :=
  ⟨sufficiency T Allowed B allowed closed refocusing invariant det reasonable safe robust rel,
    sufficiency_converse T Allowed B allowed closed refocusing invariant det reasonable safeConverse robustConverse rel⟩
end Hypernets.Linear.ConcreteObservations
