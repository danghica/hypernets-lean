import Hypernets.Copying.AllocationCost

/-! Allocation regressions on the original term translation and arbitrary hosts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AllocationCoherenceExamples
open Graph Combined

/-- The literal translated ref term exposes its original allocation head. -/
theorem reference_head (n : Nat) : MatchEmbedding.HeadAt (Allocation.referenceGraph n)
    (.input 0) (Allocation.referenceHead n) (.operation (.unary .ref)) := ⟨rfl,List.mem_cons_self⟩

/-- The full machine performs the literal allocation while preserving its distributors. -/
theorem reference_allocate (n : Nat) :
    Combined.Step ⟨Allocation.referenceGraph n,(.rewrite,.input 0)⟩
      ⟨Allocation.allocatedGraph n,(.search,.input 0)⟩ :=
  allocation_step (.allocate_suffix (Allocation.constantArgument n) (Allocation.constantArgument_stable n)
    (Translation.singleUse 0 0 0))

/-- Every successor of the literal ref computation agrees with the constructed allocation result. -/
theorem reference_successor (n : Nat) {t : Combined.State 0 [.term] []}
    (step : Combined.Step ⟨Allocation.referenceGraph n,(.rewrite,.input 0)⟩ t) :
    Nonempty (StateIso t ⟨Allocation.allocatedGraph n,(.search,.input 0)⟩) :=
  allocation_step_deterministic (reference_head n) step (reference_allocate n)

/-- The unchanged Figure 16 translation has exactly the successful cost five,
under the full combined relation, including all alternative contextual matches. -/
theorem reference_exact_cost (n cost : Nat) :
    TerminatesIn cost ⟨Allocation.referenceGraph n,(.search,.input 0)⟩ ↔ cost = 5 := by
  have returned : Search.Step (Allocation.allocatedGraph n) (.search,.input 0) (.backtrack,.input 0) :=
    Allocation.returns_suffix (Allocation.constantArgument n) (Translation.singleUse 0 0 0)
  rw [search_cost_iff (Allocation.reference_enter n)]
  simp only [search_cost_iff (Allocation.reference_value n),
    search_cost_iff (Allocation.reference_ready n),
    allocation_cost_spectrum (reference_head n) (reference_allocate n)]
  simp only [Translation.depth] at *
  simp only [search_cost_iff returned]
  simp only [
    final_cost_iff (show (machine 0 [.term] []).final
      ⟨Allocation.allocatedGraph n,(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,hz⟩; omega
  · rintro rfl; exact ⟨4,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩

/-- The same unique successful cost holds in the allowance-indexed unbounded machine. -/
theorem reference_unbounded_exact_cost (n cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial (Combined.Examples.referenceProgram n)) t ∧
      unboundedMachine.final t) ↔ cost = 5 := by
  constructor
  · rintro ⟨t,run,done⟩
    obtain ⟨b,eq,run'⟩ := run_bounded run ⟨Allocation.referenceGraph n,(.search,.input 0)⟩ rfl
    subst t
    exact (reference_exact_cost n cost).mp ⟨b,run',done⟩
  · intro eq; subst cost
    exact ⟨_,Combined.Examples.reference_run n,rfl,trivial⟩

/-- No finite depth padding introduces an alternative successful cost for ref n. -/
theorem reference_padded_exact_cost (n layers cost : Nat) :
    (∃ t, unboundedMachine.Steps cost (execution.initial ((Combined.Examples.referenceProgram n).pad layers)) t ∧
      unboundedMachine.final t) ↔ cost = 5 :=
  (initial_cost_pad_iff _ layers cost).trans (reference_unbounded_exact_cost n cost)

/-- A ref redex in any well-typed host has the expected successor, even when
another matching proof chooses a different retained host or graph decomposition. -/
theorem host_allocation_successor {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (hi : (alphabet d).signature.input (C.edgeLabel hole) = [.term])
    (G : Hypernet d [.term] ((alphabet d).signature.output (C.edgeLabel hole)))
    (stable : Stable G) {t}
    (step : Combined.Step (plugState C hole ⟨(Allocation.before G).reboundary hi.symm rfl,
      (.rewrite,Port.cast hi.symm rfl (.input 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(Allocation.after G).reboundary hi.symm rfl,
      (.search,Port.cast hi.symm rfl (.input 0))⟩)) := by
  exact allocation_step_deterministic ((MatchEmbedding.plug C hole _).head
    (head_reboundary hi.symm rfl (Allocation.head_at G))) step
    (step_plug C hole (.rewrite (rewrite_reboundary hi.symm rfl (.local (.allocate G stable)))))
end Hypernets.Copying.AllocationCoherenceExamples
