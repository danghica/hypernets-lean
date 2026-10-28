import Hypernets.Copying.NullaryRobustness
import Hypernets.Copying.AddressedWitness

/-! Exact execution consequences of proved nullary-template robustness.
Observations use the actual copying machine and unrestricted original contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- Every original closed recursive filling has an initial lifting for the
unrestricted specimen system, with no admissibility premise on its context. -/
theorem FillingWitness.allContexts_initial_lifting {T : PreTemplate} (closed : T.OutputClosed)
    {d} {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) :
    (Specimens.system T Specimens.allContexts closed).Lifting
      (StateClass.ofState ⟨d,G,(.search,.input 0)⟩)
      (StateClass.ofState ⟨d,H,(.search,.input 0)⟩) := by
  let S := w.specimen left right (.search,.input 0) rfl
  have l := w.specimen_left left right (.search,.input 0) rfl
  have r := w.specimen_right left right (.search,.input 0) rfl
  refine ⟨S,.inl (by change Focus.search ≠ Focus.rewrite; decide),?_,?_,l.symm,r.symm⟩
  · change StateClass.Rooted (StateClass.ofState S.leftState)
    rw [l]
    exact Search.rooted_initial G 0
  · change StateClass.Rooted (StateClass.ofState S.rightState)
    rw [r]
    exact Search.rooted_initial H 0

namespace NullaryExecution
variable {T : PreTemplate} (none : T.NoInputs) (padding : T.PaddingClosed)
include none padding

/-- Nullary paired fillings have exact quantitative equivalence, using proved
input safety and both proved robustness directions of the original machine. -/
theorem filling_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  have lifting := w.allContexts_initial_lifting none.outputClosed left right
  exact ⟨Specimens.sufficiency T Specimens.allContexts none.outputClosed CostOrder.reasonable_exact
      (none.inputSafe _ _ _) (none.robust padding _ _ _) lifting,
    Specimens.sufficiency_converse T Specimens.allContexts none.outputClosed CostOrder.reasonable_exact
      (none.inputSafe _ _ _) (none.robust_converse padding _ _ _) lifting⟩

/-- Successful termination agrees at every exact transition count, including
contexts whose other computations may diverge or become stuck. -/
theorem filling_termination_count {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) := by
  have eq := filling_exact_equiv none padding w left right
  constructor
  · rintro ⟨s,run,final⟩
    obtain ⟨m,t,cost,run',final'⟩ := eq.1 run final
    cases cost
    exact ⟨t,run',final'⟩
  · rintro ⟨t,run,final⟩
    obtain ⟨m,s,cost,run',final'⟩ := eq.2 run final
    cases cost
    exact ⟨s,run',final'⟩

/-- An actual template pair can be replaced at any original addressed site,
including under boxes, in every closed observing graph. No binding restriction
or bound on the surrounding depth is imposed. -/
theorem addressed_exact_equiv {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : T.Rel G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  filling_exact_equiv none padding ((FillingWitness.of_rel 0 pair).plugAt site free) left right

/-- The addressed-context consequence preserves exact successful-transition
counts for each actual replacement, not merely termination after forgetting costs. -/
theorem addressed_termination_count {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : T.Rel G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,plugAt site G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,plugAt site H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  filling_termination_count none padding ((FillingWitness.of_rel 0 pair).plugAt site free) left right n
end NullaryExecution
end Hypernets.Copying
