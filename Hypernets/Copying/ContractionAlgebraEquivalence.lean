import Hypernets.Copying.SharingExecution
import Hypernets.Copying.ContractionAlgebraLaws

/-! The complete original Assoc/Comm template is robust in both directions and has
exact-cost contextual consequences for term and atom sharing alike. -/
namespace Hypernets.Copying.ContractionAlgebra
open Graph Combined

/-- Full robustness covers every original local rule in unrestricted contexts. -/
theorem template_robust (kind : Kind) (Q P U : CostOrder) :
    (Specimens.system (template kind) Specimens.allContexts (template_outputClosed kind)).Robust Q P U :=
  PreTemplate.SharingTrees.robust (template_sharingTrees kind) (template_paddingClosed kind) Q P U

/-- The converse uses original opposite specimens and actual matching rewrites. -/
theorem template_robust_converse (kind : Kind) (Q P U : CostOrder) :
    (Specimens.system (template kind) Specimens.allContexts (template_outputClosed kind)).opposite.Robust Q P U :=
  PreTemplate.SharingTrees.robust_converse (template_sharingTrees kind) (template_paddingClosed kind) Q P U

/-- The full original input-safety clause is proved for both sharing sorts,
including stuck entered requests and exact two/two matched copying prefixes. -/
theorem template_inputSafe (kind : Kind) (Q P : CostOrder) :
    (Specimens.system (template kind) Specimens.allContexts (template_outputClosed kind)).InputSafe Q P :=
  PreTemplate.SharingTrees.inputSafe (template_sharingTrees kind) (template_paddingClosed kind) Q P

/-- Arbitrarily many shallow or deep Assoc/Comm occurrences preserve exact execution
cost, with no assumption that their common context is binding-free. -/
theorem filling_exact_equiv (kind : Kind) {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness (template kind) G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  SharingExecution.filling_exact_equiv (template_sharingTrees kind) (template_paddingClosed kind) w left right

/-- The full closed paired-filling statement retains every successful count. -/
theorem filling_termination_count (kind : Kind) {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness (template kind) G H) (left : HoleFree G) (right : HoleFree H) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  SharingExecution.filling_termination_count (template_sharingTrees kind) (template_paddingClosed kind) w left right n

/-- Every actual Assoc/Comm pair can be replaced inside any original closed graph,
at any box depth and for either wire sort. Independent carrier renamings are
already included in the pair relation. -/
theorem addressed_exact_equiv (kind : Kind) {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : UpToIso kind G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  SharingExecution.addressed_exact_equiv (template_sharingTrees kind) (template_paddingClosed kind) site free pair left right

/-- Assoc/Comm preserves exact successful-transition counts in all such observing
contexts, including contexts with state, copying or divergent callbacks. -/
theorem addressed_termination_count (kind : Kind) {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : UpToIso kind G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,plugAt site G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,plugAt site H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  SharingExecution.addressed_termination_count (template_sharingTrees kind) (template_paddingClosed kind) site free pair left right n
end Hypernets.Copying.ContractionAlgebra
