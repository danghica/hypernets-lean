import Hypernets.Graph.ExpansionSequential
import Hypernets.Graph.AlternatingFillings

/-! Ordinary substitution realizes both sides of the alternating two-hole example. -/
namespace Hypernets.Linear.AlternatingFillings
open Graph

/-- Both pointwise output-closed families can be executed by at most two
ordinary substitutions, with the correct expanded graph as their result. -/
theorem sequential_realizations :
    (∃ n D, n ≤ 2 ∧ ShallowRun ops 0 [.term] [.term] context n D ∧
      Nonempty (Net.Iso D (context.expand left))) ∧
    (∃ n D, n ≤ 2 ∧ ShallowRun ops 0 [.term] [.term] context n D ∧
      Nonempty (Net.Iso D (context.expand right))) := by
  constructor
  · exact ExpansionSequential.realize context left
  · exact ExpansionSequential.realize context right

/-- The schedules may start at different holes. They nevertheless produce
the same graph class when they realize the same prescribed family. -/
theorem reverse_schedule (H : (e : context.Edge) → Hypernet ops 0
    ((alphabet ops 0).signature.input (context.edgeLabel e))
    ((alphabet ops 0).signature.output (context.edgeLabel e))) :
    ∃ n m D E, n ≤ 1 ∧ m ≤ 1 ∧
      ExpansionSequential.Execution (context.plug 0 (H 0)) (Net.ExpansionPeel.rest context H 0) n D ∧
      ExpansionSequential.Execution (context.plug 1 (H 1)) (Net.ExpansionPeel.rest context H 1) m E ∧ Nonempty (Net.Iso D E) := by
  have cover : ∀ e : context.Edge, e ∈ [0,1] := by
    intro e
    have h := e.isLt
    have eq : e = 0 ∨ e = 1 := by
      have : e.val = 0 ∨ e.val = 1 := by omega
      rcases this with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases eq with rfl | rfl <;> simp
  obtain ⟨n,D,bn,l⟩ := ExpansionSequential.realize_list
    (context.plug 0 (H 0)) (Net.ExpansionPeel.rest context H 0)
    (ExpansionSequential.remaining context H 0 [1])
    (ExpansionSequential.remaining_copies context H 0 [1]
      (fun e absent => False.elim (absent (cover e))))
  obtain ⟨m,E,bm,r⟩ := ExpansionSequential.realize_list
    (context.plug 1 (H 1)) (Net.ExpansionPeel.rest context H 1)
    (ExpansionSequential.remaining context H 1 [0])
    (ExpansionSequential.remaining_copies context H 1 [0]
      (fun e absent => False.elim (absent (by
        have h := cover e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        exact h.symm))))
  have lcount := ExpansionSequential.remaining_length context H 0 [1]
  have rcount := ExpansionSequential.remaining_length context H 1 [0]
  refine ⟨n,m,D,E,by simpa using Nat.le_trans bn lcount,
    by simpa using Nat.le_trans bm rcount,l,r,?_⟩
  exact (ExpansionSequential.Execution.step context H 0 l).order_independent
    (ExpansionSequential.Execution.step context H 1 r)

end Hypernets.Linear.AlternatingFillings
