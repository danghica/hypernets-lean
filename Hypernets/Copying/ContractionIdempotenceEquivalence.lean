import Hypernets.Copying.NullaryExecution
import Hypernets.Copying.ContractionIdempotenceLaws

/-! The complete original Idem template is robust in both directions and has
exact-cost contextual consequences for term and atom sharing alike. -/
namespace Hypernets.Copying.ContractionIdempotence
open Graph Combined

/-- Full robustness covers every original local rule in unrestricted contexts. -/
theorem template_robust (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust Q P U :=
  template_noInputs.robust template_paddingClosed Q P U

/-- The converse uses original opposite specimens and actual matching rewrites. -/
theorem template_robust_converse (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust Q P U :=
  template_noInputs.robust_converse template_paddingClosed Q P U

/-- Arbitrarily many shallow or deep Idem occurrences preserve exact execution
cost, with no assumption that their common context is binding-free. -/
theorem filling_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  NullaryExecution.filling_exact_equiv template_noInputs template_paddingClosed w left right

/-- The full closed paired-filling statement retains every successful count. -/
theorem filling_termination_count {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  NullaryExecution.filling_termination_count template_noInputs template_paddingClosed w left right n

/-- Every actual Idem pair can be replaced inside any original closed graph,
at any box depth and for either wire sort. Independent carrier renamings are
already included in the pair relation. -/
theorem addressed_exact_equiv {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : UpToIso G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  NullaryExecution.addressed_exact_equiv template_noInputs template_paddingClosed site free pair left right

/-- Idem preserves exact successful-transition counts in all such observing
contexts, including contexts with state, copying or divergent callbacks. -/
theorem addressed_termination_count {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : UpToIso G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,plugAt site G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,plugAt site H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  NullaryExecution.addressed_termination_count template_noInputs template_paddingClosed site free pair left right n
end Hypernets.Copying.ContractionIdempotence
