import Hypernets.Graph.ClassSpecimenSystem

/-! The paper's safety and robustness clauses evaluated on the class machine. -/
namespace Hypernets.Linear
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
namespace DeepStateClass
/-- Focus mode is invariant under recursive focus-preserving isomorphism. -/
def mode (s : DeepStateClass ops d) : Focus :=
  Quotient.liftOn s (fun s => s.focussed.mode) (fun _ _ ⟨a⟩ => a.mode)
end DeepStateClass

namespace ClassSafety
variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (B : Behaviour ops d kind)

/-- The unconditional witness and mode agreement of a quasi-specimen, with
conditional rooted comparisons, now evaluated on state classes. -/
def Quasi (A R : DeepStateClass ops d → DeepStateClass ops d → Prop)
    (s t : DeepStateClass ops d) : Prop :=
  ∃ S : DeepSpecimen T Allowed,
    S.focus.mode = s.mode ∧ S.focus.mode = t.mode ∧
      (DeepStateClass.Rooted kind s → DeepStateClass.Rooted kind t →
        State.Rooted kind S.leftState ∧ State.Rooted kind S.rightState ∧
        A s (DeepStateClass.ofState S.leftState) ∧ R (DeepStateClass.ofState S.rightState) t)

/-- Safety and robustness use quasi-specimens away from rewrite mode. -/
def NonRewriteQuasi (A R : DeepStateClass ops d → DeepStateClass ops d → Prop)
    (s t : DeepStateClass ops d) : Prop := s.mode ≠ .rewrite ∧ Quasi T Allowed (kind := kind) A R s t

/-- All three input-safety alternatives, without restricting to rooted specimens. -/
def InputSafe (Q P : CostOrder) : Prop :=
  ∀ S : DeepSpecimen T Allowed, S.focus.mode = .search → S.focus.Entering →
    (∃ k l s t, (UAMClasses.machine B).Steps k (DeepStateClass.ofState S.leftState) s ∧
      (UAMClasses.machine B).Stuck s ∧
      (UAMClasses.machine B).Steps l (DeepStateClass.ofState S.rightState) t ∧ (UAMClasses.machine B).Stuck t) ∨
    (∃ (D : DeepSpecimen T Allowed) (k l : Nat), ConcreteSafety.Settled T Allowed D ∧ Q.rel (1+k) l ∧
      (UAMClasses.machine B).Steps (1+k) (DeepStateClass.ofState S.leftState) (DeepStateClass.ofState D.leftState) ∧
      (UAMClasses.machine B).Steps l (DeepStateClass.ofState S.rightState) (DeepStateClass.ofState D.rightState)) ∨
    (∃ k l s t, Q.rel (1+k) (1+l) ∧
      (UAMClasses.machine B).Steps (1+k) (DeepStateClass.ofState S.leftState) s ∧
      (UAMClasses.machine B).Steps (1+l) (DeepStateClass.ofState S.rightState) t ∧
      NonRewriteQuasi T Allowed (kind := kind) ((UAMClasses.machine B).Equiv P) ((UAMClasses.machine B).Equiv P) s t)

/-- Robustness at every remote rewrite specimen. The unrooted alternative is
retained, and every full-class successor is quantified, regardless of its names. -/
def Robust (Q P R : CostOrder) : Prop :=
  ∀ S : DeepSpecimen T Allowed, S.focus.mode = .rewrite → ¬ S.focus.Entering →
    ∀ {u}, UAMClasses.Step B (DeepStateClass.ofState S.leftState) u →
      (¬ State.Rooted kind S.leftState ∨ ¬ State.Rooted kind S.rightState) ∨
      (∃ k z, (UAMClasses.machine B).Steps k u z ∧ (UAMClasses.machine B).Stuck z) ∨
      ∃ k l s t, Q.rel (1+k) l ∧ (UAMClasses.machine B).Steps k u s ∧
        (UAMClasses.machine B).Steps l (DeepStateClass.ofState S.rightState) t ∧
        NonRewriteQuasi T Allowed (kind := kind) ((UAMClasses.machine B).Refines P) ((UAMClasses.machine B).Refines R) s t

variable (allowed : IsoClosedContexts Allowed) (closed : (T d).OutputClosed)
    (refocusing : RefocusingStates kind B.step)

/-- The stronger class quasi-specimen yields the abstract rooted consequence. -/
theorem quasi_bridge {A R s t} (q : NonRewriteQuasi T Allowed (kind := kind) A R s t) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).Quasi A R s t := by
  intro hs ht
  obtain ⟨mode,S,sm,_,witness⟩ := q
  exact ⟨S,fun h => mode (sm.symm.trans h),witness hs ht⟩

/-- No graph locality hypothesis is added when transporting class input safety. -/
theorem inputSafe_bridge {Q P} (safe : InputSafe T Allowed B Q P) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).InputSafe Q P := by
  intro S _ _ mode entering
  rcases safe S mode entering with stuck | direct | quasi
  · exact .inl stuck
  · exact .inr (.inl direct)
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := quasi
    exact .inr (.inr ⟨k,l,s,t,cost,ls,rs,quasi_bridge T Allowed B allowed closed refocusing q⟩)

/-- Rootedness rules out precisely the concrete unrooted robustness alternative. -/
theorem robust_bridge {Q P R} (robust : Robust T Allowed B Q P R) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).Robust Q P R := by
  intro S hl hr mode remote u step
  rcases robust S mode remote step with bad | stuck | matching
  · exact False.elim (bad.elim (fun h => h hl) (fun h => h hr))
  · exact .inl stuck
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := matching
    exact .inr ⟨k,l,s,t,cost,ls,rs,quasi_bridge T Allowed B allowed closed refocusing q⟩

/-- Concrete forward Proposition 40: the class lifting is a counting simulation. -/
theorem countingSimulation {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q P) (robust : Robust T Allowed B Q P R) :
    (UAMClasses.machine B).CountingSimulation Q P R
      (ClassSpecimens.system T Allowed B allowed closed refocusing).Lifting :=
  (ClassSpecimens.system T Allowed B allowed closed refocusing).countingSimulation
    (fun {_ _ _} l r => UAMClasses.deterministic B invariant det l r) reasonable
    (inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (robust_bridge T Allowed B allowed closed refocusing robust)

include allowed closed refocusing in
/-- Concrete remote rooted specimens satisfy quantitative refinement on the
full class machine. General initial contextual lifting is still separate. -/
theorem sufficiency {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q P) (robust : Robust T Allowed B Q P R)
    (S : DeepSpecimen T Allowed) (remote : ConcreteSafety.Remote T Allowed S)
    (hl : State.Rooted kind S.leftState) (hr : State.Rooted kind S.rightState) :
    (UAMClasses.machine B).Refines Q (DeepStateClass.ofState S.leftState) (DeepStateClass.ofState S.rightState) :=
  (countingSimulation T Allowed B allowed closed refocusing invariant det reasonable safe robust).sound
    (fun {_ _ _} l r => UAMClasses.deterministic B invariant det l r) reasonable ⟨S,remote,hl,hr,rfl,rfl⟩
end ClassSafety
end Hypernets.Linear
