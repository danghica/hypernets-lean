import Hypernets.Copying.CombinedLowering
import Hypernets.Copying.CombinedPaddingExecution

/-! Exact padding invariance for the concrete combined execution. Both formerly
abstract representation obligations are now discharged for this machine. -/
namespace Hypernets.Copying.Combined

/-- Arbitrary unbounded runs from a padded state reflect at their original cost. -/
theorem unbounded_run_reflect_padding {s t : UnboundedState} {n}
    (run : unboundedMachine.Steps n (padUnbounded s) t) :
    ∃ u, unboundedMachine.Steps n s u ∧ Represents (padUnbounded u) t := by
  obtain ⟨b,endEq,bounded⟩ := run_bounded run (padState s.2) rfl
  subst t
  obtain ⟨u,smaller,⟨iso⟩⟩ := run_reflect_padding bounded
  exact ⟨⟨s.1,u⟩,run_unbounded smaller,.lift iso⟩

/-- No new successful execution cost is introduced by padding. -/
theorem padding_refines_reverse (Q : CostOrder) (s : UnboundedState) :
    unboundedMachine.Refines Q (padUnbounded s) s := by
  intro n t run done
  obtain ⟨u,smaller,iso⟩ := unbounded_run_reflect_padding run
  exact ⟨n,u,Q.refl n,smaller,(represents_final iso).mpr done⟩

/-- Padding equivalence holds for every cost preorder, including exact equality. -/
theorem padding_equiv (Q : CostOrder) (s : UnboundedState) :
    unboundedMachine.Equiv Q s (padUnbounded s) :=
  ⟨padding_refines Q s,padding_refines_reverse Q s⟩

/-- Every finite allowance increase preserves all successful costs in both directions. -/
theorem initial_pad_equiv (Q : CostOrder) (P : ClosedProgram) (n : Nat) :
    unboundedMachine.Equiv Q (execution.initial P) (execution.initial (P.pad n)) := by
  induction n with
  | zero => exact ⟨Machine.Refines.refl _ _,Machine.Refines.refl _ _⟩
  | succ n ih =>
    have one := padding_equiv Q (execution.initial (P.pad n))
    rw [padding_initial] at one
    exact ⟨ih.1.trans one.1,one.2.trans ih.2⟩

/-- The concrete execution now discharges the previously open padding interface. -/
theorem execution_respectsPadding : execution.RespectsPadding :=
  fun P => initial_pad_equiv CostOrder.any P 1

/-- Equality of the entire successful-cost spectrum, without any uniqueness assumption. -/
theorem initial_cost_pad_iff (P : ClosedProgram) (layers cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial (P.pad layers)) t ∧ unboundedMachine.final t) ↔
    (∃ t, unboundedMachine.Steps cost (execution.initial P) t ∧ unboundedMachine.final t) := by
  constructor
  · rintro ⟨t,run,done⟩
    obtain ⟨j,u,eq,run',done'⟩ := (initial_pad_equiv CostOrder.exact P layers).2 run done
    cases eq; exact ⟨u,run',done'⟩
  · rintro ⟨t,run,done⟩
    obtain ⟨j,u,eq,run',done'⟩ := (initial_pad_equiv CostOrder.exact P layers).1 run done
    cases eq; exact ⟨u,run',done'⟩

/-- Termination, and therefore its negation, is independent of unused depth. -/
theorem terminates_pad_iff (P : ClosedProgram) (n : Nat) :
    execution.Terminates (P.pad n) ↔ execution.Terminates P := by
  constructor
  · rintro ⟨k,t,run,final⟩
    obtain ⟨j,u,_,smaller,done⟩ := (initial_pad_equiv CostOrder.exact P n).2 run final
    exact ⟨j,u,smaller,done⟩
  · exact terminates_pad P n

/-- Padding the closing context and its fragment preserves exact successful costs. -/
theorem close_pad_equiv (Q : CostOrder) {d k h} (C : ClosingContext d k h)
    (G : OpenProgram d k h) (n : Nat) :
    unboundedMachine.Equiv Q (execution.initial (C.close G))
      (execution.initial ((C.pad n).close (G.pad n))) := by
  have padded := initial_pad_equiv Q (C.close G) n
  have renamed := initial_iso Q ((C.close G).pad n).focusFree ((C.close G).pad n).holeFree
    ((C.pad n).close (G.pad n)).focusFree ((C.pad n).close (G.pad n)).holeFree (C.pad_close_iso G n)
  exact ⟨padded.1.trans renamed.1,renamed.2.trans padded.2⟩

/-- Contextual equivalence at a larger allowance reflects to the original one. -/
theorem equiv_of_pad {d k h} {G H : OpenProgram d k h} (n : Nat)
    (rel : execution.Equiv CostOrder.any (G.pad n) (H.pad n)) :
    execution.Equiv CostOrder.any G H :=
  execution.equiv_of_pad execution_respectsIso execution_respectsPadding n rel

/-- Arbitrarily large common allowances suffice for the unchanged term translation. -/
theorem observationalEquiv_iff_cofinal {k h} (t u : Term k h) :
    ObservationalEquiv execution t u ↔
      ∀ b, ∃ N, b ≤ N ∧ ∃ ht : Translation.depth t ≤ N, ∃ hu : Translation.depth u ≤ N,
        execution.Equiv CostOrder.any (translatedProgram t N ht) (translatedProgram u N hu) :=
  Copying.observationalEquiv_iff_cofinal execution execution_respectsIso execution_respectsPadding t u

/-- Full term-context congruence for the concrete execution, with no remaining
isomorphism or padding assumptions and no equal-minimum-depth restriction. -/
theorem observationalEquiv_context {v a k h} (C : TermContext v a k h)
    (t u : Term v a) (rel : ObservationalEquiv execution t u) :
    ObservationalEquiv execution (C.fill t) (C.fill u) :=
  Copying.observationalEquiv_context execution execution_respectsIso execution_respectsPadding C t u rel

end Hypernets.Copying.Combined
