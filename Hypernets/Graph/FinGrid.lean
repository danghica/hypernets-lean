import Hypernets.Graph.Finite

/-! Ordered finite grids: columns label resources and rows label their uses. -/
namespace Hypernets.Graph
namespace FinGrid

/-- Row-major index: resource i in use j occurs at i + k*j. -/
def index {k m} (i : Fin k) (j : Fin m) : Fin (k*m) :=
  ⟨i.val + k*j.val,by
    have h := Nat.add_lt_add_right i.isLt (k*j.val)
    have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt j.isLt)
    exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_add, Nat.add_comm] using h) bound⟩

/-- The index decomposition also covers empty grids, whose inverse domain is empty. -/
def split {k m} (n : Fin (k*m)) : Σ _ : Fin k, Fin m := by
  have pos : 0 < k := by
    cases k with
    | zero => have h := n.isLt; simp at h
    | succ k => omega
  exact ⟨⟨n.val % k,Nat.mod_lt _ pos⟩,
    ⟨n.val / k,(Nat.div_lt_iff_lt_mul pos).mpr (by simpa [Nat.mul_comm] using n.isLt)⟩⟩

theorem split_index {k m} (i : Fin k) (j : Fin m) : split (index i j) = ⟨i,j⟩ := by
  apply Sigma.ext
  · apply Fin.ext
    simp [split, index, Nat.mod_eq_of_lt i.isLt]
  · apply heq_of_eq
    apply Fin.ext
    simp [split, index, Nat.add_mul_div_left i.val j.val (show 0 < k by have h := i.isLt; omega), Nat.div_eq_of_lt i.isLt]

theorem index_split {k m} (n : Fin (k*m)) : index (split n).1 (split n).2 = n := by
  apply Fin.ext
  exact Nat.mod_add_div _ _

def bijection (k m : Nat) : Bijection (Σ _ : Fin k, Fin m) (Fin (k*m)) where
  toFun p := index p.1 p.2
  invFun := split
  left_inv p := split_index p.1 p.2
  right_inv := index_split

/-- The resource coordinate is recovered by remainder. -/
theorem index_mod {k m} (i : Fin k) (j : Fin m) : (index i j).val % k = i.val := by
  simp [index, Nat.mod_eq_of_lt i.isLt]

/-- The use coordinate is recovered by quotient. -/
theorem index_div {k m} (i : Fin k) (j : Fin m) : (index i j).val / k = j.val := by
  simp [index, Nat.add_mul_div_left i.val j.val (show 0 < k by have h := i.isLt; omega), Nat.div_eq_of_lt i.isLt]
end FinGrid
end Hypernets.Graph
