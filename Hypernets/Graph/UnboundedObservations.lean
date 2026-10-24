import Hypernets.Graph.UnboundedConverse

/-! Independent observations and both contextual sufficiency clauses on the union. -/
namespace Hypernets.Linear.Unbounded
open ObservationFillings
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- An original observation context may have any finite depth and nested holes. -/
def ObservationContext (slots : Slots) :=
  (n : Nat) × ConcreteObservations.ObservationContext (ops := ops) (d := n) slots

/-- Independently fill and initialise the concrete context, then forget its depth.
The definition mentions neither a template nor a paired specimen. -/
noncomputable def observations (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop) :
    Observations (State ops) Slots (Fragments (ops := ops)) (ObservationContext (ops := ops)) where
  allowed c := Allowed c.1 c.2.net.val
  observe c a s := ∃ u : DeepStateClass ops c.1, ofClass u = s ∧
    (ConcreteObservations.observations (Allowed c.1)).observe c.2 a u

variable (T : LayeredPreTemplate ops) (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop)
    (B : Behaviour ops kind) (allowed : ∀ n, IsoClosedContexts (Allowed n))
    (closed : ∀ n, (T n).OutputClosed) (refocusing : B.Refocusing)

/-- Independent related observations construct a remote rooted concrete specimen. -/
theorem initial_lifting {slots : Slots} {a b : Fragments (ops := ops) slots}
    (rel : Related T a b) (c : ObservationContext (ops := ops) slots) {s t}
    (hc : (observations Allowed).allowed c) (hs : (observations Allowed).observe c a s)
    (ht : (observations Allowed).observe c b t) :
    (system T Allowed B allowed closed refocusing).Lifting s t := by
  obtain ⟨n,c⟩ := c
  obtain ⟨u,hu,hs⟩ := hs
  obtain ⟨v,hv,ht⟩ := ht
  obtain ⟨S,remote,hl,hr,us,vs⟩ :=
    ConcreteObservations.initial_lifting T (Allowed n) (B.atDepth n) (allowed n) (closed n)
      (B.refocusingAt refocusing n) rel c hc hs ht
  refine ⟨⟨n,S⟩,remote,hl,hr,?_,?_⟩
  · exact hu.symm.trans (congrArg ofClass us)
  · exact hv.symm.trans (congrArg ofClass vs)

include allowed closed refocusing in
/-- Forward contextual sufficiency for the actual unbounded full UAM. -/
theorem sufficiency {Q P R : CostOrder} (det : B.Deterministic) (reasonable : Reasonable Q P R)
    (safe : Safety.InputSafe T Allowed B Q P) (robust : Safety.Robust T Allowed B Q P R)
    {slots : Slots} {a b : Fragments (ops := ops) slots} (rel : Related T a b) :
    (observations Allowed).Refines (machine B) Q a b :=
  (system T Allowed B allowed closed refocusing).contextual_sufficiency
    (observations Allowed) (Related T)
    (fun {_ _ _} rel c {_ _} hc hs ht => initial_lifting T Allowed B allowed closed refocusing rel c hc hs ht)
    (deterministic B det) reasonable
    (Safety.inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (Safety.robust_bridge T Allowed B allowed closed refocusing robust) rel

include allowed closed refocusing in
/-- Converse contextual sufficiency on the same unbounded full UAM. -/
theorem sufficiency_converse {Q P R : CostOrder} (det : B.Deterministic) (reasonable : Reasonable Q P R)
    (safe : Safety.InputSafe T Allowed B Q.converse P)
    (robust : Safety.ConverseRobust T Allowed B Q P R)
    {slots : Slots} {a b : Fragments (ops := ops) slots} (rel : Related T a b) :
    (observations Allowed).Refines (machine B) Q b a :=
  (system T Allowed B allowed closed refocusing).contextual_sufficiency_converse
    (observations Allowed) (Related T)
    (fun {_ _ _} rel c {_ _} hc hs ht => initial_lifting T Allowed B allowed closed refocusing rel c hc hs ht)
    (deterministic B det) reasonable
    (Safety.inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (Safety.converseRobust_bridge T Allowed B allowed closed refocusing robust) rel

include allowed closed refocusing in
/-- Both quantitative contextual clauses, with no bound fixed for executions. -/
theorem equivalence {Q P R : CostOrder} (det : B.Deterministic) (reasonable : Reasonable Q P R)
    (safe : Safety.InputSafe T Allowed B Q P) (safeConverse : Safety.InputSafe T Allowed B Q.converse P)
    (robust : Safety.Robust T Allowed B Q P R)
    (robustConverse : Safety.ConverseRobust T Allowed B Q P R)
    {slots : Slots} {a b : Fragments (ops := ops) slots} (rel : Related T a b) :
    (observations Allowed).Equiv (machine B) Q a b :=
  ⟨sufficiency T Allowed B allowed closed refocusing det reasonable safe robust rel,
    sufficiency_converse T Allowed B allowed closed refocusing det reasonable safeConverse robustConverse rel⟩
end Hypernets.Linear.Unbounded
