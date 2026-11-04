import Hypernets.Copying.DistributorExtension
import Hypernets.Copying.OccurrenceBoundaryTarget

/-! Separate the added resource's canonical unary row from the actual
single-use environment distributor, retaining every original resource. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SingleUseExtension
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (outputIndex termResource atomResource outputIndex_term outputIndex_atom)

/-- The literal single-use graph with equality transport made explicit. -/
def raw (d k h : Nat) : Hypernet d (environmentInterface k h) (environmentInterface k h) :=
  (Translation.environmentDistributor d k h 1).reboundary (by simp) rfl

theorem original (d k h : Nat) : Translation.singleUse d k h = raw d k h :=
  cast_eq_reboundary _ _ _

/-- All old rows embed, with their original use and resource coordinates. -/
noncomputable def retained (d k h : Nat) (s : ShareSort) :
    Occurrence (raw d k h) (raw d (variables s k) (atoms s h)) :=
  ((DistributorExtension.distributor d k h 1 s).reboundarySource (by simp) rfl).reboundaryTarget (by simp) rfl

theorem retained_output (d k h : Nat) (s : ShareSort)
    (i : Fin (environmentInterface k h).length) :
    (retained d k h s).ports (.output i) = .output (outputIndex s i) := by
  change Port.cast (show environmentInterface (variables s k*1) (atoms s h*1) = _ by simp) rfl ((DistributorExtension.distributor d k h 1 s).ports (.output i)) = _
  rw [DistributorExtension.distributor_output]
  rfl

theorem retained_input (d k h : Nat) (s : ShareSort)
    (i : Fin (environmentInterface k h).length) :
    (retained d k h s).ports (.input i) = .input (outputIndex s i) := by
  by_cases bound : i.val < k
  · let j : Fin k := ⟨i.val,bound⟩
    have eq : i = EnvironmentPermutation.termIndex (h := h) j := rfl
    rw [eq,outputIndex_term]
    change Port.cast (show environmentInterface (variables s k*1) (atoms s h*1) = environmentInterface (variables s k) (atoms s h) by simp) rfl
      ((DistributorExtension.distributor d k h 1 s).ports
        (.input (EnvironmentPermutation.termIndex ⟨j.val+k*0,(FinGrid.index j (0 : Fin 1)).isLt⟩))) = _
    erw [DistributorExtension.distributor_term_input d k h 1 s j (0 : Fin 1)]
    rfl
  · let j : Fin h := ⟨i.val-k,by have := i.isLt; simp [environmentInterface] at this; omega⟩
    have eq : i = EnvironmentPermutation.atomIndex (k := k) j := Fin.ext (by dsimp [j,EnvironmentPermutation.atomIndex]; omega)
    rw [eq,outputIndex_atom]
    change Port.cast (show environmentInterface (variables s k*1) (atoms s h*1) = environmentInterface (variables s k) (atoms s h) by simp) rfl
      ((DistributorExtension.distributor d k h 1 s).ports (.input ⟨k+j.val,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate,Nat.mul_one]; omega⟩)) = _
    have idx : (⟨k+j.val,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate,Nat.mul_one]; omega⟩ : Fin (environmentInterface (k*1) (h*1)).length) =
        EnvironmentPermutation.atomIndex ⟨j.val+h*0,(FinGrid.index j (0 : Fin 1)).isLt⟩ :=
      Fin.ext (by simp [EnvironmentPermutation.atomIndex])
    rw [idx]
    erw [DistributorExtension.distributor_atom_input d k h 1 s j (0 : Fin 1)]
    apply congrArg Port.input
    apply Fin.ext
    simp [Port.cast,EnvironmentPermutation.atomIndex]

/-- The sole new row is the last variable row or the first atom row. -/
def added (d k h : Nat) (s : ShareSort) :
    Occurrence (CanonicalTree.atDepth s 1 d) (raw d (variables s k) (atoms s h)) :=
  (DistributorExtension.selected d k h 1 s).reboundaryTarget (by simp) rfl

theorem added_input (d k h : Nat) (s : ShareSort) (i : Fin 1) :
    (added d k h s).ports (.input ⟨i.val,by simp⟩) = .input (CopyRow.addedOutput k h s) := by
  have z : i = 0 := Subsingleton.elim _ _
  subst i
  cases s
  · rfl
  · apply congrArg Port.input
    apply Fin.ext
    simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,
      Distributor.inputIndex,FinGrid.index,CopyRow.addedOutput]

theorem added_output (d k h : Nat) (s : ShareSort) (i : Fin 1) :
    (added d k h s).ports (.output i) = .output (CopyRow.addedOutput k h s) := by
  have z : i = 0 := Subsingleton.elim _ _
  subst i
  cases s
  · rfl
  · apply congrArg Port.output
    apply Fin.ext
    simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,
      CopyRow.addedOutput]

private def finCast {a b : Nat} (e : a = b) : Bijection (Fin a) (Fin b) where
  toFun := Fin.cast e
  invFun := Fin.cast e.symm
  left_inv _ := rfl
  right_inv _ := rfl

private theorem label_cast {A B : List Wire} (eq : A = B) (i : Fin A.length) :
    B[(finCast (congrArg List.length eq)).toFun i] = A[i] := by
  cases eq
  rfl

/-- Ordered insertion acts identically on both ends of the unary forest. -/
def boundary (k h : Nat) (s : ShareSort) :
    Net.Parallel.Boundary
      (Net.Tensor.interfaces (environmentInterface k h) [s.wire])
      (Net.Tensor.interfaces (environmentInterface k h) [s.wire])
      (environmentInterface (variables s k) (atoms s h))
      (environmentInterface (variables s k) (atoms s h)) where
  inputs := ((insertionBoundary [] (List.replicate k .term) (List.replicate h .atom) s).outputs).trans
    (finCast (congrArg List.length (extended_interface s k h)))
  outputs := ((insertionBoundary [] (List.replicate k .term) (List.replicate h .atom) s).outputs).trans
    (finCast (congrArg List.length (extended_interface s k h)))
  input_label b i := (label_cast (extended_interface s k h) _).trans
    ((insertionBoundary [] (List.replicate k .term) (List.replicate h .atom) s).output_label b i)
  output_label b i := (label_cast (extended_interface s k h) _).trans
    ((insertionBoundary [] (List.replicate k .term) (List.replicate h .atom) s).output_label b i)


theorem boundary_old (k h : Nat) (s : ShareSort) (i : Fin (environmentInterface k h).length) :
    (boundary k h s).inputs.toFun ⟨false,i⟩ = outputIndex s i :=
  Fin.ext (inserted_old_output s i)

theorem boundary_added (k h : Nat) (s : ShareSort) (i : Fin 1) :
    (boundary k h s).inputs.toFun ⟨true,i⟩ = CopyRow.addedOutput k h s := by
  have z : i = 0 := Subsingleton.elim _ _
  subst i
  exact Fin.ext ((inserted_weakening_output (I := []) (A := List.replicate k .term) (B := List.replicate h .atom) s).trans (by simp [CopyRow.addedOutput]))

/-- All retained rows and the new row occur disjointly in the original forest. -/
noncomputable def components (d k h : Nat) (s : ShareSort) (b : Bool) :
    Occurrence (Net.Tensor.family (raw d k h) (CanonicalTree.atDepth s 1 d) b)
      (raw d (variables s k) (atoms s h)) :=
  match b with | false => retained d k h s | true => added d k h s

private theorem retained_disjoint (d k h : Nat) (s : ShareSort)
    (e : (raw d k h).Edge) (c : (CanonicalTree.atDepth s 1 d).Edge) :
    (retained d k h s).edges e ≠ (added d k h s).edges c := by
  intro eq
  cases d <;> cases s <;> rcases e with ⟨b,e⟩ <;> cases b <;> rcases e with ⟨i,e⟩
  all_goals first
    | cases eq
    | (have same := congrArg Fin.val (congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2))
       change i.val = k at same
       have := i.isLt
       omega)
    | (have same := congrArg Fin.val (congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2))
       change i.val+1 = 0 at same
       omega)

/-- The assembled occurrence covers both groups, with no duplicated row. -/
noncomputable def occurrence (d k h : Nat) (s : ShareSort) :
    Occurrence
      (Net.Parallel.net (Net.Tensor.family (raw d k h) (CanonicalTree.atDepth s 1 d))
        (boundary k h s) ⟨[false,true],by intro b; cases b <;> simp⟩)
      (raw d (variables s k) (atoms s h)) := by
  apply Occurrence.ParallelJoin.occurrence _ _ _ (components d k h s)
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · exact retained_disjoint d k h s e c eq
  · exact retained_disjoint d k h s c e eq.symm
  · exact ne rfl

private theorem occurrence_input (d k h : Nat) (s : ShareSort) :
    ∀ i, (occurrence d k h s).ports (.input i) = .input i := by
  intro i
  obtain ⟨⟨b,j⟩,rfl⟩ : ∃ p, (boundary k h s).inputs.toFun p = i :=
    ⟨(boundary k h s).inputs.invFun i,(boundary k h s).inputs.right_inv i⟩
  change (occurrence d k h s).ports (Net.Parallel.embed _ (boundary k h s) b (.input j)) = _
  unfold occurrence
  rw [Occurrence.ParallelJoin.occurrence_embed]
  cases b
  · exact (retained_input d k h s j).trans (congrArg Port.input (boundary_old k h s j).symm)
  · exact (added_input d k h s j).trans (congrArg Port.input (boundary_added k h s j).symm)

private theorem occurrence_output (d k h : Nat) (s : ShareSort) :
    ∀ i, (occurrence d k h s).ports (.output i) = .output i := by
  intro i
  obtain ⟨⟨b,j⟩,rfl⟩ : ∃ p, (boundary k h s).outputs.toFun p = i :=
    ⟨(boundary k h s).outputs.invFun i,(boundary k h s).outputs.right_inv i⟩
  change (occurrence d k h s).ports (Net.Parallel.embed _ (boundary k h s) b (.output j)) = _
  unfold occurrence
  rw [Occurrence.ParallelJoin.occurrence_embed]
  cases b
  · exact (retained_output d k h s j).trans (congrArg Port.output (boundary_old k h s j).symm)
  · exact (added_output d k h s j).trans (congrArg Port.output (boundary_added k h s j).symm)

/-- Every original edge belongs either to a retained resource or to the added
resource; this is exhaustive even when either old environment is empty. -/
theorem edge_coverage (d k h : Nat) (s : ShareSort) :
    Function.Surjective (occurrence d k h s).edges := by
  cases d
  all_goals
   cases s with
   | term =>
     rintro ⟨b,e⟩
     cases b with
     | false =>
       rcases e with ⟨i,e⟩
       by_cases lt : i.val < k
       · exact ⟨⟨false,⟨false,⟨⟨i.val,lt⟩,e⟩⟩⟩,rfl⟩
       · have last : i = (⟨k,Nat.lt_succ_self k⟩ : Fin (k+1)) := Fin.ext (by change i.val = k; have := i.isLt; change i.val < k+1 at this; omega)
         refine ⟨⟨true,e⟩,?_⟩
         change (⟨false,⟨⟨k,_⟩,e⟩⟩ : (raw _ (k+1) h).Edge) = _
         exact congrArg (fun j : Fin (k+1) => (⟨false,⟨j,e⟩⟩ : (raw _ (k+1) h).Edge)) last.symm
     | true =>
       rcases e with ⟨i,e⟩
       exact ⟨⟨false,⟨true,⟨i,e⟩⟩⟩,rfl⟩
   | atom =>
     rintro ⟨b,e⟩
     cases b with
     | false =>
       rcases e with ⟨i,e⟩
       exact ⟨⟨false,⟨false,⟨i,e⟩⟩⟩,rfl⟩
     | true =>
       rcases e with ⟨i,e⟩
       by_cases z : i.val = 0
       · have zero : i = ⟨0,by omega⟩ := Fin.ext z
         refine ⟨⟨true,e⟩,?_⟩
         change (⟨true,⟨⟨0,_⟩,e⟩⟩ : (raw _ k (h+1)).Edge) = _
         exact congrArg (fun j : Fin (h+1) => (⟨true,⟨j,e⟩⟩ : (raw _ k (h+1)).Edge)) zero.symm
       · let j : Fin h := ⟨i.val-1,by have := i.isLt; change i.val < h+1 at this; omega⟩
         refine ⟨⟨false,⟨true,⟨j,e⟩⟩⟩,?_⟩
         change (⟨true,⟨⟨j.val+1,_⟩,e⟩⟩ : (raw _ k (h+1)).Edge) = _
         have ij : (⟨j.val+1,by have := j.isLt; omega⟩ : Fin (h+1)) = i := Fin.ext (by dsimp [j]; omega)
         exact congrArg (fun j : Fin (h+1) => (⟨true,⟨j,e⟩⟩ : (raw _ k (h+1)).Edge)) ij

/-- Exact row extraction for the unchanged Figure 16 single-use distributor.
All boundary ports are fixed; every edge and recursive label is covered. -/
noncomputable def iso (d k h : Nat) (s : ShareSort) :
    DeepIso
      (Net.Parallel.net (Net.Tensor.family (Translation.singleUse d k h) (CanonicalTree.atDepth s 1 d))
        (boundary k h s) ⟨[false,true],by intro b; cases b <;> simp⟩)
      (Translation.singleUse d (variables s k) (atoms s h)) := by
  rw [original,original]
  exact (occurrence d k h s).iso_of_edge_surjective
    (occurrence_input d k h s) (occurrence_output d k h s) (edge_coverage d k h s)

end Hypernets.Copying.SingleUseExtension
