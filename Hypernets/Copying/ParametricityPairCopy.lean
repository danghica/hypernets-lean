import Hypernets.Copying.ParametricityLiteralCopy

/-! Every original parametricity pair and every ordered member admit a
complete actual remote copying diagram. Only the original independent graph
representations and proved arithmetic interface equalities are transported. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined ContractionTree
namespace LiteralCopy

/-- The complete literal family diagram includes every large and small
input, including the last member and a family with either block empty. -/
theorem all_inputs {a b} (d m n : Nat) (P : ContractionTree .term (a+1))
    (C : ContractionTree .term (m+n)) (count : m+n=b+1) (j : Fin (b+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate ((a+1)+b) .term) [],
      Rewrite (Graft.net (P.atDepth (d+2)) ((left d C).reboundary (congrArg (fun n => List.replicate n Wire.term) count) rfl) j)
        (.input ⟨0,by simp;omega⟩) A (.input ⟨0,by simp;omega⟩) ∧
      Rewrite (Graft.net (P.atDepth (d+2)) ((right d m n).reboundary (congrArg (fun n => List.replicate n Wire.term) count) rfl) j)
        (.input ⟨0,by simp;omega⟩) B (.input ⟨0,by simp;omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  by_cases selected : j.val < m
  · cases m with
    | zero => omega
    | succ m =>
      have arity : b=m+n := by omega
      subst b
      exact large d m n P C ⟨j.val,selected⟩
  · cases n with
    | zero => have bound := j.isLt;omega
    | succ n =>
      have arity : b=m+n := by omega
      subst b
      let i : Fin (n+1) := ⟨j.val-m,by have bound:=j.isLt;omega⟩
      have result := small d m n P C i
      have atInput : (⟨m+i.val,by have:=i.isLt;omega⟩ : Fin ((m+n)+1)) = j :=
        Fin.ext (by dsimp [i];omega)
      rw [atInput] at result
      exact result

end LiteralCopy

/-- General original interfaces are first identified by their proved pair;
its literal constructor then supplies the complete copying diagram. -/
private theorem pair_copy_core {d a I O}
    (P : ContractionTree .term (a+1)) {G H : Hypernet d I O}
    (pair : Pair G H) (b : Nat) (hi : I=List.replicate (b+1) .term) (j : Fin (b+1)) :
    ∃ X Y : Hypernet d (List.replicate ((a+1)+b) .term) O,
      Rewrite (Graft.net (s := .term) (P.atDepth d) (G.reboundary hi rfl) j)
        (.input ⟨0,by simp;omega⟩) X (.input ⟨0,by simp;omega⟩) ∧
      Rewrite (Graft.net (s := .term) (P.atDepth d) (H.reboundary hi rfl) j)
        (.input ⟨0,by simp;omega⟩) Y (.input ⟨0,by simp;omega⟩) ∧
      Nonempty (FillingWitness template X Y) := by
  cases pair with
  | witness l literal r =>
    cases literal with
    | @families m n d C =>
      have count : m+n=b+1 := by
        have eq := congrArg List.length hi
        simpa only [List.length_replicate] using eq
      obtain ⟨X,Y,left,right,w⟩ := LiteralCopy.all_inputs d m n P C count j
      have li := Graft.congr (DeepIso.refl (P.atDepth (d+2)))
        (CopyRule.reboundaryIso l hi rfl) j
      have ri := Graft.congr (DeepIso.refl (P.atDepth (d+2)))
        (CopyRule.reboundaryIso r hi rfl) j
      exact ⟨X,Y,left.rename li.symm (DeepIso.refl X),right.rename ri (DeepIso.refl Y),w⟩

/-- Every independently represented original Figure20 pair and every one of
its ordered inputs has actual opposite remote-copy steps and a genuine
original-template residual. No selected-member or source-isolation hypothesis
remains at this public boundary. -/
theorem Pair.graft_diagram {d a b}
    (P : ContractionTree .term (a+1))
    {G H : Hypernet d (List.replicate (b+1) .term) []}
    (pair : Pair G H) (j : Fin (b+1)) :
    ∃ X Y : Hypernet d (List.replicate ((a+1)+b) .term) [],
      Rewrite (Graft.net (s := .term) (P.atDepth d) G j)
        (.input ⟨0,by simp;omega⟩) X (.input ⟨0,by simp;omega⟩) ∧
      Rewrite (Graft.net (s := .term) (P.atDepth d) H j)
        (.input ⟨0,by simp;omega⟩) Y (.input ⟨0,by simp;omega⟩) ∧
      Nonempty (FillingWitness template X Y) := by
  have result := pair_copy_core P pair b rfl j
  rw [Net.reboundary_refl G,Net.reboundary_refl H] at result
  exact result

end Hypernets.Copying.Parametricity
