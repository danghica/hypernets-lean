import Hypernets.Copying.ParametricityGraphs
import Hypernets.Copying.BoxPullWeakeningReverseBeta
import Hypernets.Copying.OccurrenceBoundaryTarget

/-! Indexed complete occurrences of the original ordered abstraction copies.
The recursion is the literal Figure20 family construction, including empty
families; no alternate translation or family-order convention is introduced. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyComponents
open Graph Opening
variable {d k : Nat} (G : Hypernet d [.term] (List.replicate k .term))

/-- The selected original member of a finite ordered family. -/
noncomputable def copy : (m : Nat) → Fin m → Occurrence G (copies G m)
  | 0,i => Fin.elim0 i
  | m+1,i => if zero : i.val = 0 then
      (BoxPullWeakening.ReverseComponents.tensorLeft G (copies G m)).reboundaryTarget
        (by simp [List.replicate_succ])
        (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm])
    else (copy m ⟨i.val-1,by omega⟩).comp
      ((BoxPullWeakening.ReverseComponents.tensorRight G (copies G m)).reboundaryTarget
        (by simp [List.replicate_succ])
        (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm]))

/-- Every copy consumes precisely its original ordered external input. -/
theorem copy_input (m : Nat) (i : Fin m) :
    (copy G m i).ports (.input 0) = .input ⟨i.val,by simp⟩ := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    unfold copy
    split
    · rename_i zero
      exact congrArg Port.input (Fin.ext zero.symm)
    · rename_i nonzero
      change Port.cast (by simp [List.replicate_succ])
        (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm])
        ((BoxPullWeakening.ReverseComponents.tensorRight G (copies G m)).ports
          ((copy G m ⟨i.val-1,by omega⟩).ports (.input 0))) = _
      rw [ih]
      apply congrArg Port.input
      apply Fin.ext
      change 1+(i.val-1) = i.val
      omega

/-- All outputs of a copy keep their within-copy order and the copy blocks
remain ordered; for the paper's families k is respectively one or zero. -/
theorem copy_output (m : Nat) (i : Fin m)
    (j : Fin (List.replicate k Wire.term).length) :
    (copy G m i).ports (.output j) =
      .output ⟨k*i.val+j.val,by
        have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
        have h := j.isLt
        simp only [Nat.mul_succ,List.length_replicate] at *
        omega⟩ := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    unfold copy
    split
    · rename_i zero
      apply congrArg Port.output
      apply Fin.ext
      change j.val = k*i.val+j.val
      rw [zero,Nat.mul_zero,Nat.zero_add]
    · rename_i nonzero
      change Port.cast (by simp [List.replicate_succ])
        (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm])
        ((BoxPullWeakening.ReverseComponents.tensorRight G (copies G m)).ports
          ((copy G m ⟨i.val-1,by omega⟩).ports (.output j))) = _
      rw [ih]
      apply congrArg Port.output
      apply Fin.ext
      change (List.replicate k Wire.term).length+(k*(i.val-1)+j.val)=k*i.val+j.val
      simp only [List.length_replicate]
      have value : i.val = (i.val-1)+1 := by omega
      calc
        k+(k*(i.val-1)+j.val) = k*((i.val-1)+1)+j.val := by rw [Nat.mul_add,Nat.mul_one]; omega
        _ = k*i.val+j.val := by rw [← value]

/-- Different original members have disjoint complete edge sets, including
recursive lambda box edges. -/
theorem copy_disjoint (m : Nat) (i j : Fin m) (different : i ≠ j) :
    ∀ e f, (copy G m i).edges e ≠ (copy G m j).edges f := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    intro e f eq
    by_cases iz : i.val = 0 <;> by_cases jz : j.val = 0
    · exact different (Fin.ext (iz.trans jz.symm))
    · simp only [copy,iz,jz,↓reduceDIte,Occurrence.reboundaryTarget,
        Occurrence.comp,BoxPullWeakening.ReverseComponents.tensorLeft,
        BoxPullWeakening.ReverseComponents.tensorRight] at eq
      have impossible : false = true := congrArg Sigma.fst eq
      cases impossible
    · simp only [copy,iz,jz,↓reduceDIte,Occurrence.reboundaryTarget,
        Occurrence.comp,BoxPullWeakening.ReverseComponents.tensorLeft,
        BoxPullWeakening.ReverseComponents.tensorRight] at eq
      have impossible : true = false := congrArg Sigma.fst eq
      cases impossible
    · have ne : (⟨i.val-1,by omega⟩ : Fin m) ≠ ⟨j.val-1,by omega⟩ := by
        intro eq
        apply different
        apply Fin.ext
        have val : i.val-1 = j.val-1 := congrArg Fin.val eq
        omega
      apply ih _ _ ne e f
      have changed : (⟨true,(copy G m ⟨i.val-1,by omega⟩).edges e⟩ :
          (Net.Tensor.net G (copies G m)).Edge) = ⟨true,(copy G m ⟨j.val-1,by omega⟩).edges f⟩ := by
        simpa only [copy,iz,jz,↓reduceDIte,Occurrence.comp,Occurrence.reboundaryTarget,
          BoxPullWeakening.ReverseComponents.tensorRight,Occurrence.ParallelJoin.component,
          copies,Function.comp_apply] using eq
      exact eq_of_heq (Sigma.mk.inj changed).2

/-- Every actual family edge belongs to one of its original indexed members;
zero families contribute no hidden identity or administrative edge. -/
theorem copy_cover (m : Nat) (e : (copies G m).Edge) :
    ∃ i : Fin m, ∃ a : G.Edge, (copy G m i).edges a = e := by
  induction m with
  | zero => exact Empty.elim e
  | succ m ih =>
    obtain ⟨side,e⟩ := e
    cases side
    · exact ⟨⟨0,by omega⟩,e,rfl⟩
    · obtain ⟨i,a,eq⟩ := ih e
      refine ⟨⟨i.val+1,by omega⟩,a,?_⟩
      simp only [copy,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceDIte,
        Nat.add_sub_cancel]
      change (⟨true,(copy G m i).edges a⟩ : (Net.Tensor.net G (copies G m)).Edge) = ⟨true,e⟩
      rw [eq]

end Hypernets.Copying.Parametricity.FamilyComponents
