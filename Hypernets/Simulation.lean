import Hypernets.Quantitative

/-! Appendix F: the definition of counting simulation and Proposition 37. -/

namespace Hypernets.Machine

variable {State : Type u} (M : Machine State)

/-- Refinement on either side of a candidate relation (in path order). -/
def UpTo (P S : CostOrder) (R : State → State → Prop) (s t : State) : Prop :=
  ∃ u v, M.Refines P s u ∧ R u v ∧ M.Refines S v t

/-- Appendix F, conditions (A), (B)(I), and (B)(II), including the stuck branch. -/
structure CountingSimulation (Q P S : CostOrder) (R : State → State → Prop) : Prop where
  final_match : ∀ {s t}, R s t → M.final s → M.final t
  progress : ∀ {s t s'}, R s t → M.step s s' →
    (∃ k z, M.Steps k s' z ∧ M.Stuck z) ∨
    ∃ k l h₁ h₂, M.Steps k s' h₁ ∧ M.Steps l t h₂ ∧
      Q.rel (1 + k) l ∧ M.UpTo P S R h₁ h₂

variable {M}

/-- Proposition 37, generalized from UAM states to any deterministic machine. -/
theorem CountingSimulation.sound {Q P S : CostOrder} {R : State → State → Prop}
    (det : M.Deterministic) (reasonable : Reasonable Q P S)
    (sim : M.CountingSimulation Q P S R) {s t : State} (related : R s t) :
    M.Refines Q s t := by
  intro n z run hz
  induction n using Nat.strongRecOn generalizing s t z with
  | ind n ih =>
      cases run with
      | zero => exact ⟨0, t, Q.refl 0, .zero t, sim.final_match related hz⟩
      | @cons n s s' z ss' tail =>
          rcases sim.progress related ss' with stuck | matching
          · obtain ⟨k, w, path, hw⟩ := stuck
            exact False.elim (path.not_stuck_of_final det tail hz hw)
          · obtain ⟨k, l, h₁, h₂, path₁, path₂, cost, u, v, before, rel, after⟩ := matching
            obtain ⟨r, count, finish⟩ := path₁.prefix_of_final det tail hz
            obtain ⟨a, za, ra, runa, finala⟩ := before finish hz
            have smaller : a < n + 1 := by
              have bound := reasonable.left_decreases ra
              omega
            obtain ⟨b, zb, ab, runb, finalb⟩ := ih a smaller rel runa finala
            obtain ⟨c, zc, bc, runc, finalc⟩ := after runb finalb
            have rc : Q.rel r c := reasonable.sandwich ra ab bc
            have total : Q.rel (n + 1) (l + c) := by
              have added := reasonable.additive cost rc
              have eq : 1 + k + r = n + 1 := by omega
              rw [eq] at added
              exact added
            exact ⟨l + c, zc, total, path₂.append runc, finalc⟩

end Hypernets.Machine
