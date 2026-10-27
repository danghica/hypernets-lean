import Hypernets.Copying.DerivationFillings
import Hypernets.Copying.BPermExactExecution

/-! Exact execution semantics of finite structural BPerm derivations. Each link
is discharged by the proved full robustness theorem for original specimens;
transitivity is used only for quantitative machine equivalence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

/-- Closed finite chains preserve exact successful-run counts. Hole freedom of
all intermediate graphs follows from their original filling certificates. -/
theorem FillingChain.exact_equiv {d} {G H : Hypernet d [.term] []}
    (c : FillingChain G H) (closed : HoleFree G) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  have safe (n : Nat) : HoleFree (c.graph n) := (c.allLabels _ n).mp closed
  have initial (n : Nat) : unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,c.graph n,(.search,.input 0)⟩ := by
    induction n with
    | zero =>
      rw [c.start]
      exact ⟨Machine.Refines.refl _ _,Machine.Refines.refl _ _⟩
    | succ n ih =>
      have link := filling_exact_equiv (c.step n) (safe n) (safe (n+1))
      exact ⟨ih.1.trans link.1,link.2.trans ih.2⟩
  have result := initial c.length
  rw [c.finish c.length (Nat.le_refl _)] at result
  exact result

/-- An explicit count-by-count formulation includes all finite successful runs,
without assuming that either graph, or an arbitrary continuation, terminates. -/
theorem FillingChain.termination_count {d} {G H : Hypernet d [.term] []}
    (c : FillingChain G H) (closed : HoleFree G) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) := by
  have eq := c.exact_equiv closed
  constructor
  · rintro ⟨a,run,done⟩
    obtain ⟨m,b,cost,run',done'⟩ := eq.1 run done
    cases cost
    exact ⟨b,run',done'⟩
  · rintro ⟨b,run,done⟩
    obtain ⟨m,a,cost,run',done'⟩ := eq.2 run done
    cases cost
    exact ⟨a,run',done'⟩

/-- Semantic soundness of every structural BPerm derivation on closed,
focus-free programs, with the original unbounded machine and exact costs. -/
theorem Derivation.exact_equiv {d} {G H : Hypernet d [.term] []}
    (s : Derivation G H) (free : FocusFree G) (closed : HoleFree G) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  (s.fillingChain free).exact_equiv closed

theorem Derivation.termination_count {d} {G H : Hypernet d [.term] []}
    (s : Derivation G H) (free : FocusFree G) (closed : HoleFree G) (n : Nat) :
    (∃ a, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ a ∧ unboundedMachine.final a) ↔
    (∃ b, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ b ∧ unboundedMachine.final b) :=
  (s.fillingChain free).termination_count closed n

end Hypernets.Copying.BoxPermutation
