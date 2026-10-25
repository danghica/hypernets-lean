import Hypernets.Graph.Paths

/-! A strictly increasing edge rank excludes cycles in a concrete graph. -/
namespace Hypernets.Graph.Net
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (G : Net σ I O) (rank : G.Edge → Nat)
    (increase : ∀ {e f}, G.Adjacent e f → rank e < rank f)

include increase in
theorem path_rank_strict {es : List G.Edge} (path : G.Path es)
    {i j : Nat} (hi : i < es.length) (hj : j < es.length) (ij : i < j) :
    rank es[i] < rank es[j] := by
  induction es generalizing i j with
  | nil => simp at hi
  | cons e es ih =>
    cases es with
    | nil => simp at hi hj; omega
    | cons f es =>
      obtain ⟨adj,tail⟩ := path_pair_iff.mp path
      have step := increase adj
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j =>
          cases j with
          | zero => exact step
          | succ j =>
            exact Nat.lt_trans step
              (ih tail (i := 0) (j := j+1) (by simp) (by simpa using hj) (by omega))
      | succ i =>
        cases j with
        | zero => omega
        | succ j => exact ih tail (by simpa using hi) (by simpa using hj) (by omega)

include rank increase in
/-- A rank increasing on adjacency makes every finite path edge-simple. -/
theorem path_nodup_of_rank {es : List G.Edge} (path : G.Path es) : es.Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  by_cases h : i = j
  · exact h
  apply False.elim
  rcases Nat.lt_or_gt_of_ne h with lt | gt
  · have h := path_rank_strict G rank increase path hi hj lt
    rw [eq] at h
    exact Nat.lt_irrefl _ h
  · have h := path_rank_strict G rank increase path hj hi gt
    rw [eq] at h
    exact Nat.lt_irrefl _ h
end Hypernets.Graph.Net
