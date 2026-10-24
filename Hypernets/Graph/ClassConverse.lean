import Hypernets.Graph.ClassSafety

/-! Concrete reverse Proposition 40 on the full class machine. -/
namespace Hypernets.Linear
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
namespace ClassSafety
variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (B : Behaviour ops d kind)

/-- A quasi-specimen with its actual two filling vectors exchanged. The witness
remains an original specimen; comparisons run into its right and out of its left. -/
def ConverseQuasi (A R : DeepStateClass ops d → DeepStateClass ops d → Prop)
    (s t : DeepStateClass ops d) : Prop :=
  s.mode ≠ .rewrite ∧
  ∃ S : DeepSpecimen T Allowed,
    S.focus.mode = s.mode ∧ S.focus.mode = t.mode ∧
      (DeepStateClass.Rooted kind s → DeepStateClass.Rooted kind t →
        State.Rooted kind S.rightState ∧ State.Rooted kind S.leftState ∧
        A s (DeepStateClass.ofState S.rightState) ∧ R (DeepStateClass.ofState S.leftState) t)

/-- Reversing both comparison relations and the endpoints recovers the original
quasi-specimen predicate, including its unconditional witness and mode clauses. -/
theorem converseQuasi_iff {A R s t} :
    ConverseQuasi T Allowed (kind := kind) A R s t ↔
      NonRewriteQuasi T Allowed (kind := kind) (fun x y => R y x) (fun x y => A y x) t s := by
  constructor
  · rintro ⟨mode,S,sm,tm,w⟩
    refine ⟨fun h => mode (sm.symm.trans (tm.trans h)),S,tm,sm,?_⟩
    intro ht hs
    obtain ⟨hr,hl,a,r⟩ := w hs ht
    exact ⟨hl,hr,r,a⟩
  · rintro ⟨mode,S,tm,sm,w⟩
    refine ⟨fun h => mode (tm.symm.trans (sm.trans h)),S,sm,tm,?_⟩
    intro hs ht
    obtain ⟨hl,hr,r,a⟩ := w ht hs
    exact ⟨hr,hl,a,r⟩

/-- Equivalence comparisons can be reversed without changing their cost order.
This is the direction needed by safety III in the converse proof. -/
theorem converseQuasi_equiv {P : CostOrder} {s t}
    (q : NonRewriteQuasi T Allowed (kind := kind)
      ((UAMClasses.machine B).Equiv P) ((UAMClasses.machine B).Equiv P) s t) :
    ConverseQuasi T Allowed (kind := kind)
      ((UAMClasses.machine B).Equiv P) ((UAMClasses.machine B).Equiv P) t s := by
  apply (converseQuasi_iff T Allowed).mpr
  obtain ⟨mode,S,sm,tm,w⟩ := q
  refine ⟨mode,S,sm,tm,?_⟩
  intro hs ht
  obtain ⟨hl,hr,a,r⟩ := w hs ht
  exact ⟨hl,hr,⟨a.2,a.1⟩,⟨r.2,r.1⟩⟩

/-- Robustness on the converse template, represented by the original specimens
with right and left exchanged. No symmetry of the original relation is assumed. -/
def ConverseRobust (Q P R : CostOrder) : Prop :=
  ∀ S : DeepSpecimen T Allowed, S.focus.mode = .rewrite → ¬ S.focus.Entering →
    ∀ {u}, UAMClasses.Step B (DeepStateClass.ofState S.rightState) u →
      (¬ State.Rooted kind S.rightState ∨ ¬ State.Rooted kind S.leftState) ∨
      (∃ k z, (UAMClasses.machine B).Steps k u z ∧ (UAMClasses.machine B).Stuck z) ∨
      ∃ k l s t, Q.rel (1+k) l ∧ (UAMClasses.machine B).Steps k u s ∧
        (UAMClasses.machine B).Steps l (DeepStateClass.ofState S.leftState) t ∧
        ConverseQuasi T Allowed (kind := kind) ((UAMClasses.machine B).Refines P)
          ((UAMClasses.machine B).Refines R) s t

variable (allowed : IsoClosedContexts Allowed) (closed : (T d).OutputClosed)
    (refocusing : RefocusingStates kind B.step)

/-- The concrete converse witness supplies the opposite interface's quasi law. -/
theorem converseQuasi_bridge {A R s t} (q : ConverseQuasi T Allowed (kind := kind) A R s t) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).opposite.Quasi A R s t := by
  intro hs ht
  obtain ⟨mode,S,sm,_,w⟩ := q
  exact ⟨S,fun h => mode (sm.symm.trans h),w hs ht⟩

/-- Only the unrooted alternative is eliminated by restriction to rooted sources. -/
theorem converseRobust_bridge {Q P R} (robust : ConverseRobust T Allowed B Q P R) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).opposite.Robust Q P R := by
  intro S hr hl mode remote u step
  rcases robust S mode remote step with bad | stuck | matching
  · exact False.elim (bad.elim (fun h => h hr) (fun h => h hl))
  · exact .inl stuck
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := matching
    exact .inr ⟨k,l,s,t,cost,ls,rs,converseQuasi_bridge T Allowed B allowed closed refocusing q⟩

/-- Concrete reverse Proposition 40. Safety remains on the original template
with converse costs; its quasi comparisons remain equivalences. -/
theorem countingSimulation_converse {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q.converse P) (robust : ConverseRobust T Allowed B Q P R) :
    (UAMClasses.machine B).CountingSimulation Q P R
      (ClassSpecimens.system T Allowed B allowed closed refocusing).opposite.Lifting :=
  (ClassSpecimens.system T Allowed B allowed closed refocusing).countingSimulation_converse
    (fun {_ _ _} l r => UAMClasses.deterministic B invariant det l r) reasonable
    (inputSafe_bridge T Allowed B allowed closed refocusing safe)
    (converseRobust_bridge T Allowed B allowed closed refocusing robust)

include allowed closed refocusing in
/-- Reverse quantitative refinement for every remote jointly rooted specimen. -/
theorem sufficiency_converse {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q.converse P) (robust : ConverseRobust T Allowed B Q P R)
    (S : DeepSpecimen T Allowed) (remote : ConcreteSafety.Remote T Allowed S)
    (hl : State.Rooted kind S.leftState) (hr : State.Rooted kind S.rightState) :
    (UAMClasses.machine B).Refines Q (DeepStateClass.ofState S.rightState) (DeepStateClass.ofState S.leftState) :=
  (countingSimulation_converse T Allowed B allowed closed refocusing invariant det reasonable safe robust).sound
    (fun {_ _ _} l r => UAMClasses.deterministic B invariant det l r) reasonable ⟨S,remote,hr,hl,rfl,rfl⟩

include allowed closed refocusing in
/-- Both concrete sufficiency clauses together, before general contextual lifting. -/
theorem equivalence {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q P) (safeConverse : InputSafe T Allowed B Q.converse P)
    (robust : Robust T Allowed B Q P R) (robustConverse : ConverseRobust T Allowed B Q P R)
    (S : DeepSpecimen T Allowed) (remote : ConcreteSafety.Remote T Allowed S)
    (hl : State.Rooted kind S.leftState) (hr : State.Rooted kind S.rightState) :
    (UAMClasses.machine B).Equiv Q (DeepStateClass.ofState S.leftState) (DeepStateClass.ofState S.rightState) :=
  ⟨sufficiency T Allowed B allowed closed refocusing invariant det reasonable safe robust S remote hl hr,
    sufficiency_converse T Allowed B allowed closed refocusing invariant det reasonable
      safeConverse robustConverse S remote hl hr⟩
include closed refocusing in
/-- Both refinements apply to every constructed initial relocation, with
remoteness and rootedness discharged rather than supplied as hypotheses. -/
theorem initial_equivalence {Q P R : CostOrder} (invariant : B.RespectsIso)
    (det : DeterministicModulo B.step) (reasonable : Reasonable Q P R)
    (safe : InputSafe T Allowed B Q P) (safeConverse : InputSafe T Allowed B Q.converse P)
    (robust : Robust T Allowed B Q P R) (robustConverse : ConverseRobust T Allowed B Q P R)
    (S : DeepSpecimen T Allowed) :
    let D := S.relocate allowed (TypedPosition.initial S.focus.underlying)
    (UAMClasses.machine B).Equiv Q (DeepStateClass.ofState D.leftState) (DeepStateClass.ofState D.rightState) := by
  obtain ⟨hl,hr⟩ := S.relocate_initial allowed
  exact equivalence T Allowed B allowed closed refocusing invariant det reasonable
    safe safeConverse robust robustConverse _ (.inl (by intro h; cases h))
    (DeepStateClass.initial_rooted hl) (DeepStateClass.initial_rooted hr)

end ClassSafety
end Hypernets.Linear
