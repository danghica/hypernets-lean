import Hypernets.Copying.AddressedWitness
import Hypernets.Copying.DerivationExecution

/-! Semantic soundness of structural BPerm derivations in every original
binding-free closing context, including arbitrary nesting of the selected hole. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

/-- Lift each genuine certificate through the same original addressed occurrence. -/
noncomputable def FillingChain.plugAt {d I O} {C : Hypernet d I O} {r J K}
    (site : Site C r J K) (free : FocusFree C) {G H : Hypernet r J K}
    (chain : FillingChain G H) : FillingChain (Copying.plugAt site G) (Copying.plugAt site H) where
  length := chain.length
  graph n := Copying.plugAt site (chain.graph n)
  start := by rw [chain.start]
  finish n hn := by rw [chain.finish n hn]
  step n := (chain.step n).plugAt site free

/-- A structural derivation preserves exact costs in the complete observation
class. No restriction to translated term contexts or terminating callbacks is used. -/
theorem Derivation.contextual_exact {d k h} {G H : OpenProgram d k h}
    (s : Derivation G.graph H.graph) : execution.Equiv CostOrder.exact G H := by
  have eq (C : ClosingContext d k h) :=
    ((s.fillingChain G.focusFree).plugAt C.site C.bindingFree.1).exact_equiv
      (C.fill_holeFree G.graph G.holeFree)
  exact ⟨fun C => (eq C).1,fun C => (eq C).2⟩

/-- Every successful finite run has a matching run with the identical count
after placing either endpoint in an arbitrary allowed closing context. -/
theorem Derivation.contextual_count {d k h} {G H : OpenProgram d k h}
    (s : Derivation G.graph H.graph) (C : ClosingContext d k h) (n : Nat) :
    (∃ a, unboundedMachine.Steps n (execution.initial (C.close G)) a ∧ unboundedMachine.final a) ↔
    (∃ b, unboundedMachine.Steps n (execution.initial (C.close H)) b ∧ unboundedMachine.final b) :=
  ((s.fillingChain G.focusFree).plugAt C.site C.bindingFree.1).termination_count
    (C.fill_holeFree G.graph G.holeFree) n

/-- Forgetting exact costs yields the intended termination-based equivalence. -/
theorem Derivation.contextual_termination {d k h} {G H : OpenProgram d k h}
    (s : Derivation G.graph H.graph) : execution.Equiv CostOrder.any G H := by
  apply (execution.equiv_any_iff G H).mpr
  intro C
  constructor
  · rintro ⟨n,a,run,done⟩
    obtain ⟨b,run',done'⟩ := (s.contextual_count C n).mp ⟨a,run,done⟩
    exact ⟨n,b,run',done'⟩
  · rintro ⟨n,b,run,done⟩
    obtain ⟨a,run',done'⟩ := (s.contextual_count C n).mpr ⟨b,run,done⟩
    exact ⟨n,a,run',done'⟩

end Hypernets.Copying.BoxPermutation
