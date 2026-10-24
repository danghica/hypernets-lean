import Hypernets.Graph.UnboundedSafety

/-! The converse robustness clause on the same unbounded machine. -/
namespace Hypernets.Linear.Unbounded.Safety
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}
variable (T : LayeredPreTemplate ops) (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop)
    (B : Behaviour ops kind)

/-- Exchange the concrete filling vectors, retaining the original witness and modes. -/
def ConverseQuasi (A R : State ops → State ops → Prop) (s t : State ops) : Prop :=
  mode s ≠ .rewrite ∧
  ∃ S : Specimen T Allowed, S.2.focus.mode = mode s ∧ S.2.focus.mode = mode t ∧
    (Rooted kind s → Rooted kind t → Rooted kind (right S) ∧ Rooted kind (left S) ∧
      A s (right S) ∧ R (left S) t)

/-- The original paper's robustness alternative applied with right and left exchanged. -/
def ConverseRobust (Q P R : CostOrder) : Prop :=
  ∀ S : Specimen T Allowed, S.2.focus.mode = .rewrite → ¬ S.2.focus.Entering →
    ∀ {u}, UAMStep B (right S) u →
      (¬ Rooted kind (right S) ∨ ¬ Rooted kind (left S)) ∨
      (∃ k z, (machine B).Steps k u z ∧ (machine B).Stuck z) ∨
      ∃ k l s t, Q.rel (1+k) l ∧ (machine B).Steps k u s ∧ (machine B).Steps l (left S) t ∧
        ConverseQuasi T Allowed (kind := kind) ((machine B).Refines P) ((machine B).Refines R) s t

variable (allowed : ∀ n, IsoClosedContexts (Allowed n)) (closed : ∀ n, (T n).OutputClosed)
    (refocusing : B.Refocusing)

theorem converseQuasi_bridge {A R s t} (q : ConverseQuasi T Allowed (kind := kind) A R s t) :
    (system T Allowed B allowed closed refocusing).opposite.Quasi A R s t := by
  intro hs ht
  obtain ⟨mode,S,sm,_,w⟩ := q
  exact ⟨S,fun h => mode (sm.symm.trans h),w hs ht⟩

theorem converseRobust_bridge {Q P R} (robust : ConverseRobust T Allowed B Q P R) :
    (system T Allowed B allowed closed refocusing).opposite.Robust Q P R := by
  intro S hr hl mode remote u step
  rcases robust S mode remote step with bad | stuck | matching
  · exact False.elim (bad.elim (fun h => h hr) (fun h => h hl))
  · exact .inl stuck
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := matching
    exact .inr ⟨k,l,s,t,cost,ls,rs,converseQuasi_bridge T Allowed B allowed closed refocusing q⟩

/-- Reverse counting simulation, with converse costs on the original safety predicate. -/
theorem countingSimulation_converse {Q P R : CostOrder} (det : B.Deterministic)
    (reasonable : Reasonable Q P R) (safe : InputSafe T Allowed B Q.converse P)
    (robust : ConverseRobust T Allowed B Q P R) :
    (machine B).CountingSimulation Q P R (system T Allowed B allowed closed refocusing).opposite.Lifting :=
  (system T Allowed B allowed closed refocusing).countingSimulation_converse
    (deterministic B det) reasonable
    (inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (converseRobust_bridge T Allowed B allowed closed refocusing robust)
end Hypernets.Linear.Unbounded.Safety
