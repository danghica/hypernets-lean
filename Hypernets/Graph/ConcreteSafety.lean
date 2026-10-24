import Hypernets.Graph.TupleFillings
import Hypernets.Graph.UAM

/-! The unrestricted specimen predicates of paper §§8.1–8.3 on actual states. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace ConcreteSafety
variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (kind : Op → OperationKind)

/-- A concrete specimen is settled in backtrack mode or in non-entering search mode. -/
def Settled (S : DeepSpecimen T Allowed) : Prop :=
  S.focus.mode = .backtrack ∨ (S.focus.mode = .search ∧ ¬ S.focus.Entering)

/-- A remote specimen excludes precisely an entering rewrite focus. -/
def Remote (S : DeepSpecimen T Allowed) : Prop :=
  S.focus.mode ≠ .rewrite ∨ ¬ S.focus.Entering

/-- Paper §8.1: a witness specimen exists independently of rootedness; all three
focus labels agree. Only the comparison and witness-rootedness claims are conditional. -/
def Quasi (A B : State ops d → State ops d → Prop) (s t : State ops d) : Prop :=
  ∃ S : DeepSpecimen T Allowed,
    S.focus.mode = s.focussed.mode ∧ S.focus.mode = t.focussed.mode ∧
      (State.Rooted kind s → State.Rooted kind t →
        State.Rooted kind S.leftState ∧ State.Rooted kind S.rightState ∧
        A s S.leftState ∧ B S.rightState t)

/-- The quasi-specimen alternatives of safety and robustness exclude rewrite mode. -/
def NonRewriteQuasi (A B : State ops d → State ops d → Prop) (s t : State ops d) : Prop :=
  s.focussed.mode ≠ .rewrite ∧ Quasi T Allowed kind A B s t

/-- An actual specimen is a quasi-specimen up to equality, including when unrooted. -/
theorem specimen_quasi (S : DeepSpecimen T Allowed) :
    Quasi T Allowed kind Eq Eq S.leftState S.rightState := by
  exact ⟨S,rfl,rfl,fun l r => ⟨l,r,rfl,rfl⟩⟩

/-- Quasi-specimen endpoints always have the same focus mode. -/
theorem Quasi.modes {A B} {s t : State ops d} (q : Quasi T Allowed kind A B s t) :
    s.focussed.mode = t.focussed.mode := by
  obtain ⟨S,l,r,_⟩ := q
  exact l.symm.trans r

/-- Weakening the two up-to relations preserves a quasi-specimen. -/
theorem Quasi.mono {A B A' B'} {s t : State ops d} (q : Quasi T Allowed kind A B s t)
    (left : ∀ x y, A x y → A' x y) (right : ∀ x y, B x y → B' x y) :
    Quasi T Allowed kind A' B' s t := by
  obtain ⟨S,l,r,body⟩ := q
  exact ⟨S,l,r,fun hs ht => by
    obtain ⟨sl,sr,a,b⟩ := body hs ht
    exact ⟨sl,sr,left _ _ a,right _ _ b⟩⟩

/-- The rooted consequence consumed by the abstract proof is derived from the
stronger concrete definition, including the witness's non-rewrite mode. -/
theorem NonRewriteQuasi.rooted_witness {A B} {s t : State ops d}
    (q : NonRewriteQuasi T Allowed kind A B s t)
    (hs : State.Rooted kind s) (ht : State.Rooted kind t) :
    ∃ S : DeepSpecimen T Allowed, S.focus.mode ≠ .rewrite ∧
      State.Rooted kind S.leftState ∧ State.Rooted kind S.rightState ∧
      A s S.leftState ∧ B S.rightState t := by
  obtain ⟨mode,S,sm,_,body⟩ := q
  exact ⟨S,fun h => mode (sm.symm.trans h),body hs ht⟩

variable (B : Behaviour ops d kind)

/-- Paper §8.2 with all three alternatives and no rooted-source restriction. -/
def InputSafe (Q P : CostOrder) : Prop :=
  ∀ S : DeepSpecimen T Allowed, S.focus.mode = .search → S.focus.Entering →
    (∃ k l s t, (UAM.machine B).Steps k S.leftState s ∧ (UAM.machine B).Stuck s ∧
      (UAM.machine B).Steps l S.rightState t ∧ (UAM.machine B).Stuck t) ∨
    (∃ (D : DeepSpecimen T Allowed) (k l : Nat), Settled T Allowed D ∧ Q.rel (1+k) l ∧
      (UAM.machine B).Steps (1+k) S.leftState D.leftState ∧
      (UAM.machine B).Steps l S.rightState D.rightState) ∨
    (∃ k l s t, Q.rel (1+k) (1+l) ∧ (UAM.machine B).Steps (1+k) S.leftState s ∧
      (UAM.machine B).Steps (1+l) S.rightState t ∧
      NonRewriteQuasi T Allowed kind ((UAM.machine B).Equiv P) ((UAM.machine B).Equiv P) s t)

/-- Paper §8.3 relative to a fixed rewrite pair. The first alternative, absent
from the abstract rooted interface, explicitly allows an unrooted specimen side. -/
def RobustRelative (Q P R : CostOrder) (source target : State ops d) : Prop :=
  ∀ S : DeepSpecimen T Allowed, S.leftState = source →
    S.focus.mode = .rewrite → ¬ S.focus.Entering →
    (¬ State.Rooted kind S.leftState ∨ ¬ State.Rooted kind S.rightState) ∨
    (∃ k z, (UAM.machine B).Steps k target z ∧ (UAM.machine B).Stuck z) ∨
    (∃ k l s t, Q.rel (1+k) l ∧ (UAM.machine B).Steps k target s ∧
      (UAM.machine B).Steps l S.rightState t ∧
      NonRewriteQuasi T Allowed kind ((UAM.machine B).Refines P) ((UAM.machine B).Refines R) s t)

/-- Robustness for all rewrite transitions of the supplied concrete UAM. -/
def Robust (Q P R : CostOrder) : Prop :=
  ∀ s t, UAM.Rewrite B s t → RobustRelative T Allowed kind B Q P R s t

/-- Safety combines the operational input condition and pointwise output closure. -/
def Template (Q P : CostOrder) : Prop :=
  InputSafe T Allowed kind B Q P ∧ ∀ r, (T r).OutputClosed

/-- For rooted source specimens the unrooted robustness alternative is impossible.
The resulting alternatives still use the full paper quasi-specimen predicate. -/
theorem Robust.rooted {Q P R : CostOrder} (robust : Robust T Allowed kind B Q P R)
    (S : DeepSpecimen T Allowed) (hl : State.Rooted kind S.leftState)
    (hr : State.Rooted kind S.rightState) (mode : S.focus.mode = .rewrite)
    (remote : ¬ S.focus.Entering) {t} (step : UAM.Rewrite B S.leftState t) :
    (∃ k z, (UAM.machine B).Steps k t z ∧ (UAM.machine B).Stuck z) ∨
    (∃ k l s u, Q.rel (1+k) l ∧ (UAM.machine B).Steps k t s ∧
      (UAM.machine B).Steps l S.rightState u ∧
      NonRewriteQuasi T Allowed kind ((UAM.machine B).Refines P) ((UAM.machine B).Refines R) s u) := by
  rcases robust _ _ step S rfl mode remote with bad | rest
  · exact False.elim (bad.elim (fun h => h hl) (fun h => h hr))
  · exact rest

/-- Settled concrete specimens satisfy the remote predicate. -/
theorem settled_remote {S : DeepSpecimen T Allowed} (settled : Settled T Allowed S) :
    Remote T Allowed S := by
  left
  rcases settled with back | ⟨search,_⟩ <;> simp_all
end ConcreteSafety
end Hypernets.Linear
