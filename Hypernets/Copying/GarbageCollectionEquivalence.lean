import Hypernets.Copying.GarbageCollectionLaws
import Hypernets.Copying.NullaryExecution

/-! Full robustness and exact-cost contextual equivalence for Figure 21's
literal garbage-collection family, in all original observation contexts. -/
namespace Hypernets.Copying.GarbageCollection
open Graph Combined

/-- Every original local rule admits actual matching GC residuals. -/
theorem template_robust (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust Q P U :=
  template_noInputs.robust template_paddingClosed Q P U

/-- The original opposite specimen system also satisfies full robustness. -/
theorem template_robust_converse (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust Q P U :=
  template_noInputs.robust_converse template_paddingClosed Q P U

/-- Arbitrary simultaneous recursive GC fillings preserve exact successful
execution costs, without a binding restriction on their observing context. -/
theorem filling_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  NullaryExecution.filling_exact_equiv template_noInputs template_paddingClosed w left right

theorem filling_termination_count {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  NullaryExecution.filling_termination_count template_noInputs template_paddingClosed w left right n

/-- The actual GC pair can be substituted at an original site at any box
depth. Both filled graphs, rather than the nullary fragments alone, execute. -/
theorem addressed_exact_equiv {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : UpToIso G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  NullaryExecution.addressed_exact_equiv template_noInputs template_paddingClosed site free pair left right

/-- Every successful transition count is preserved in these unrestricted
contexts, including contexts with effects, copying and divergent computations. -/
theorem addressed_termination_count {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : UpToIso G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,plugAt site G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,plugAt site H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  NullaryExecution.addressed_termination_count template_noInputs template_paddingClosed site free pair left right n

end Hypernets.Copying.GarbageCollection
