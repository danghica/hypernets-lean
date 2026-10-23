import Hypernets.Transition

namespace Hypernets

/-- A preorder on execution lengths, kept explicit to avoid competing instances. -/
structure CostOrder where
  rel : Nat → Nat → Prop
  refl : ∀ n, rel n n
  trans : ∀ {a b c}, rel a b → rel b c → rel a c

/-- The three conditions of §8.4, with relational composition written explicitly. -/
structure Reasonable (Q P S : CostOrder) : Prop where
  additive : ∀ {a b c d}, Q.rel a b → Q.rel c d → Q.rel (a + c) (b + d)
  left_decreases : ∀ {a b}, P.rel a b → b ≤ a
  left_in_right : ∀ {a b}, P.rel a b → S.rel a b
  sandwich : ∀ {a b c d}, P.rel a b → Q.rel b c → S.rel c d → Q.rel a d

namespace CostOrder

def converse (Q : CostOrder) : CostOrder where
  rel a b := Q.rel b a
  refl := Q.refl
  trans ab bc := Q.trans bc ab

def exact : CostOrder := ⟨Eq, fun _ => rfl, Eq.trans⟩

def improvement : CostOrder := ⟨fun a b => b ≤ a, Nat.le_refl,
  fun ab bc => Nat.le_trans bc ab⟩

def overhead : CostOrder := ⟨Nat.le, Nat.le_refl, Nat.le_trans⟩

def any : CostOrder := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

theorem reasonable_exact : Reasonable exact exact exact where
  additive := by intros; simp_all [exact]
  left_decreases := by intros; simp_all [exact]
  left_in_right := by intros; assumption
  sandwich := by intros; simp_all [exact]

theorem reasonable_improvement : Reasonable improvement improvement improvement where
  additive := by intros; dsimp [improvement] at *; omega
  left_decreases := by intros; assumption
  left_in_right := by intros; assumption
  sandwich := by intros; dsimp [improvement] at *; omega

theorem reasonable_termination : Reasonable any improvement any where
  additive := by intros; trivial
  left_decreases := by intros; assumption
  left_in_right := by intros; trivial
  sandwich := by intros; trivial

theorem reasonable_overhead : Reasonable overhead exact exact where
  additive := by intros; dsimp [overhead] at *; omega
  left_decreases := by intros; simp_all [exact]
  left_in_right := by intros; assumption
  sandwich := by intros; simp_all [exact]

end CostOrder

namespace Machine

variable {State : Type u} (M : Machine State)

/-- §7.1: only successful termination is observed; stuckness is not termination. -/
def Refines (Q : CostOrder) (s t : State) : Prop :=
  ∀ ⦃n z⦄, M.Steps n s z → M.final z →
    ∃ m w, Q.rel n m ∧ M.Steps m t w ∧ M.final w

def Equiv (Q : CostOrder) (s t : State) : Prop :=
  M.Refines Q s t ∧ M.Refines Q t s

variable {M}

theorem Refines.refl (Q : CostOrder) (s : State) : M.Refines Q s s := by
  intro n z run hz
  exact ⟨n, z, Q.refl n, run, hz⟩

theorem Refines.trans {Q : CostOrder} {s t v : State}
    (h : M.Refines Q s t) (h' : M.Refines Q t v) : M.Refines Q s v := by
  intro n z run hz
  obtain ⟨m, w, nm, tw, hw⟩ := h run hz
  obtain ⟨k, x, mk, vx, hx⟩ := h' tw hw
  exact ⟨k, x, Q.trans nm mk, vx, hx⟩

theorem Refines.mono {Q P : CostOrder}
    (inc : ∀ {n m}, Q.rel n m → P.rel n m) {s t : State}
    (h : M.Refines Q s t) : M.Refines P s t := by
  intro n z run hz
  obtain ⟨m, w, cost, path, final⟩ := h run hz
  exact ⟨m, w, inc cost, path, final⟩

end Machine
end Hypernets
