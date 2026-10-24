import Hypernets.Graph.UnboundedSpecimens

/-! The paper's concrete safety and robustness alternatives on the unbounded machine. -/
namespace Hypernets.Linear.Unbounded
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

theorem mode_advance (i : Nat) (s : Stage ops) : (advance i s).2.mode = s.2.mode := by
  induction i with
  | zero => rfl
  | succ i ih => exact (mode_padding _).trans ih

/-- The focus mode is intrinsic to an unbounded state. -/
def mode (s : State ops) : Focus := Quotient.liftOn s (fun s => s.2.mode) (by
  intro s t h
  obtain ⟨i,j,h⟩ := h
  exact (mode_advance i s).symm.trans ((congrArg (fun s : Stage ops => s.2.mode) h).trans (mode_advance j t)))

theorem nonrewrite_iff (s : State ops) : NonRewrite s ↔ mode s ≠ .rewrite := by
  induction s using Quotient.inductionOn with | h s => rfl

namespace Safety
variable (T : LayeredPreTemplate ops) (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop)
    (B : Behaviour ops kind)

/-- Quasi-specimens retain an unconditional concrete witness and mode agreement;
the comparison obligations are conditional on rootedness of both endpoints. -/
def Quasi (A R : State ops → State ops → Prop) (s t : State ops) : Prop :=
  ∃ S : Specimen T Allowed, S.2.focus.mode = mode s ∧ S.2.focus.mode = mode t ∧
    (Rooted kind s → Rooted kind t → Rooted kind (left S) ∧ Rooted kind (right S) ∧
      A s (left S) ∧ R (right S) t)

def NonRewriteQuasi (A R : State ops → State ops → Prop) (s t : State ops) : Prop :=
  mode s ≠ .rewrite ∧ Quasi T Allowed (kind := kind) A R s t

/-- Settledness is tested on the actual context's distinguished focus. -/
def Settled (S : Specimen T Allowed) : Prop :=
  ConcreteSafety.Settled T (Allowed S.1) S.2

/-- Input safety, with its three original alternatives and unbounded executions. -/
def InputSafe (Q P : CostOrder) : Prop :=
  ∀ S : Specimen T Allowed, S.2.focus.mode = .search → S.2.focus.Entering →
    (∃ k l s t, (machine B).Steps k (left S) s ∧ (machine B).Stuck s ∧
      (machine B).Steps l (right S) t ∧ (machine B).Stuck t) ∨
    (∃ (D : Specimen T Allowed) (k l : Nat), Settled T Allowed D ∧ Q.rel (1+k) l ∧
      (machine B).Steps (1+k) (left S) (left D) ∧ (machine B).Steps l (right S) (right D)) ∨
    (∃ k l s t, Q.rel (1+k) (1+l) ∧ (machine B).Steps (1+k) (left S) s ∧
      (machine B).Steps (1+l) (right S) t ∧
      NonRewriteQuasi T Allowed (kind := kind) ((machine B).Equiv P) ((machine B).Equiv P) s t)

/-- Robustness quantifies over every global successor, including depth-increasing computation. -/
def Robust (Q P R : CostOrder) : Prop :=
  ∀ S : Specimen T Allowed, S.2.focus.mode = .rewrite → ¬ S.2.focus.Entering →
    ∀ {u}, UAMStep B (left S) u →
      (¬ Rooted kind (left S) ∨ ¬ Rooted kind (right S)) ∨
      (∃ k z, (machine B).Steps k u z ∧ (machine B).Stuck z) ∨
      ∃ k l s t, Q.rel (1+k) l ∧ (machine B).Steps k u s ∧ (machine B).Steps l (right S) t ∧
        NonRewriteQuasi T Allowed (kind := kind) ((machine B).Refines P) ((machine B).Refines R) s t

variable (allowed : ∀ n, IsoClosedContexts (Allowed n)) (closed : ∀ n, (T n).OutputClosed)
    (refocusing : B.Refocusing)

theorem quasi_bridge {A R s t} (q : NonRewriteQuasi T Allowed (kind := kind) A R s t) :
    (system T Allowed B allowed closed refocusing).Quasi A R s t := by
  intro hs ht
  obtain ⟨mode,S,sm,_,w⟩ := q
  exact ⟨S,fun h => mode (sm.symm.trans h),w hs ht⟩

/-- Transfer the three concrete safety alternatives to the proved specimen system. -/
theorem inputSafe_bridge {Q P} (safe : InputSafe T Allowed B Q P) :
    (system T Allowed B allowed closed refocusing).InputSafe Q P := by
  intro S _ _ mode entering
  rcases safe S mode entering with stuck | direct | quasi
  · exact .inl stuck
  · exact .inr (.inl direct)
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := quasi
    exact .inr (.inr ⟨k,l,s,t,cost,ls,rs,quasi_bridge T Allowed B allowed closed refocusing q⟩)

/-- Rootedness excludes exactly the unrooted robustness alternative. -/
theorem robust_bridge {Q P R} (robust : Robust T Allowed B Q P R) :
    (system T Allowed B allowed closed refocusing).Robust Q P R := by
  intro S hl hr mode remote u step
  rcases robust S mode remote step with bad | stuck | matching
  · exact False.elim (bad.elim (fun h => h hl) (fun h => h hr))
  · exact .inl stuck
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := matching
    exact .inr ⟨k,l,s,t,cost,ls,rs,quasi_bridge T Allowed B allowed closed refocusing q⟩

/-- Proposition 40 on the unbounded full UAM with concrete safety and robustness. -/
theorem countingSimulation {Q P R : CostOrder} (det : B.Deterministic) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q P) (robust : Robust T Allowed B Q P R) :
    (machine B).CountingSimulation Q P R (system T Allowed B allowed closed refocusing).Lifting :=
  (system T Allowed B allowed closed refocusing).countingSimulation (deterministic B det) reasonable
    (inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (robust_bridge T Allowed B allowed closed refocusing robust)
end Safety
end Hypernets.Linear.Unbounded
