import Hypernets.Copying.Specimens
import Hypernets.Copying.OneWayPaths

/-! The class machine has exactly the original program and term observations. -/
namespace Hypernets.Copying.Combined.StateClass

theorem terminates_iff (P : ClosedProgram) : execution.Terminates P ↔ Combined.execution.Terminates P :=
  exists_congr (fun n => successful_iff _ n)

theorem contextual_refines_iff (Q : CostOrder) {d k h} (G H : OpenProgram d k h) :
    execution.Refines Q G H ↔ Combined.execution.Refines Q G H :=
  forall_congr' (fun _C => refines_iff Q _ _)

theorem contextual_equiv_iff (Q : CostOrder) {d k h} (G H : OpenProgram d k h) :
    execution.Equiv Q G H ↔ Combined.execution.Equiv Q G H :=
  and_congr (contextual_refines_iff Q G H) (contextual_refines_iff Q H G)

/-- Every original binding-free observation context and every adequate depth is
retained; the terms and their Figure 16 translations are unchanged. -/
theorem observationalEquiv_iff {k h} (t u : Term k h) :
    ObservationalEquiv execution t u ↔ ObservationalEquiv Combined.execution t u :=
  forall_congr' (fun d => forall_congr' (fun ht => forall_congr' (fun hu =>
    contextual_equiv_iff CostOrder.any (translatedProgram t d ht) (translatedProgram u d hu))))

/-- Adding representation allowance identifies the same class, without a step. -/
theorem padding_eq (s : UnboundedState) : ofState s = ofState (padUnbounded s) :=
  Quotient.sound (Representation.padding s)

/-- No finite computation can gain or lose a successful cost by changing its
representative, including arbitrary alternating padding and renaming. -/
theorem representation_successful_iff {s t : UnboundedState} (h : Representation s t) (n : Nat) :
    (∃ u, unboundedMachine.Steps n s u ∧ unboundedMachine.final u) ↔
      ∃ u, unboundedMachine.Steps n t u ∧ unboundedMachine.final u := by
  rw [← successful_iff s n,← successful_iff t n]
  exact congrArg (fun x => ∃ u, machine.Steps n x u ∧ machine.final u) (Quotient.sound h) ▸ Iff.rfl
end Hypernets.Copying.Combined.StateClass

namespace Hypernets.Copying.Specimens
open Combined

/-- Both robustness directions yield quantitative equivalence for the actual
initial graphs of any certified recursive paired filling. -/
theorem equivalence_of_filling (T : PreTemplate) (Allowed : ∀ d, Hypernet d [.term] [] → Prop)
    (closed : T.OutputClosed) {Q P R : CostOrder} (reasonable : Reasonable Q P R)
    (safe : (system T Allowed closed).InputSafe Q P)
    (safeConverse : (system T Allowed closed).InputSafe Q.converse P)
    (robust : (system T Allowed closed).Robust Q P R)
    (robustConverse : (system T Allowed closed).opposite.Robust Q P R)
    {d} {C G H : Hypernet d [.term] []} (allowed : Allowed d C) (free : FocusFree C)
    (filling : DeepFilling T C G H) (gc : HoleFree G) (hc : HoleFree H) :
    unboundedMachine.Equiv Q ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  cases filling with
  | expand C F K edges =>
    let S : Specimen T Allowed := ⟨d,C,allowed,free,F,K,edges,gc,hc,(.search,.input 0),rfl⟩
    have lifted := initial_lifting T Allowed closed S
    exact ⟨sufficiency T Allowed closed reasonable safe robust lifted,
      sufficiency_converse T Allowed closed reasonable safeConverse robustConverse lifted⟩
end Hypernets.Copying.Specimens
