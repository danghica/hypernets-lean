import Hypernets.Copying.ParametricityFamilyIsolation

/-! Exact boundary coordinates of the original ordered abstraction families.
Small-member isolation rotates inputs and their private outputs together. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyComponents
open Graph Opening
variable {d k : Nat} (A B : Hypernet d [.term] (List.replicate k .term))

/-- Removing the first large member shifts every remaining input by one. -/
theorem remainingLarge_input (m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (remainingLarge A B m n).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
  by_cases h : i.val < m
  · have eq := Occurrence.tensorJoin_left (largeTail A B m n) (smallBlock A B (m+1) n)
      (largeTail_disjoint A B m n) (.input ⟨i.val,by simpa using h⟩)
    change (remainingLarge A B m n).ports (.input i) =
      (largeBlock A B (m+1) n).ports ((tail A m).ports (.input _)) at eq
    rw [eq,tail_input,largeBlock_input]
  · have lt : i.val-m<n := by have := i.isLt; simp only [List.length_replicate] at this; omega
    have eq := Occurrence.tensorJoin_right (largeTail A B m n) (smallBlock A B (m+1) n)
      (largeTail_disjoint A B m n) (.input ⟨i.val-m,by simpa using lt⟩)
    have represented : (BoxPullWeakening.ReverseComponents.tensorRight (copies A m) (copies B n)).ports
        (.input ⟨i.val-m,by simpa using lt⟩) = .input ⟨i.val,by have := i.isLt; simpa using this⟩ := by
      exact congrArg Port.input (Fin.ext (by change (List.replicate m Wire.term).length+(i.val-m)=i.val; simp; omega))
    rw [represented] at eq
    change (remainingLarge A B m n).ports (.input i) = _ at eq
    rw [eq,smallBlock_input]
    exact congrArg Port.input (Fin.ext (by dsimp; omega))

/-- Removing the first small member leaves the large inputs fixed and
shifts only the remaining small inputs past the removed member. -/
theorem remainingSmall_input (m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (remainingSmall A B m n).ports (.input i) =
      .input ⟨if i.val<m then i.val else i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; split <;> omega⟩ := by
  by_cases h : i.val < m
  · have eq := Occurrence.tensorJoin_left (largeBlock A B m (n+1)) (smallTail A B m n)
      (smallTail_disjoint A B m n) (.input ⟨i.val,by simpa using h⟩)
    change (remainingSmall A B m n).ports (.input i) = _ at eq
    rw [eq,largeBlock_input]
    exact congrArg Port.input (Fin.ext (by simp [h]))
  · have lt : i.val-m<n := by have := i.isLt; simp only [List.length_replicate] at this; omega
    have eq := Occurrence.tensorJoin_right (largeBlock A B m (n+1)) (smallTail A B m n)
      (smallTail_disjoint A B m n) (.input ⟨i.val-m,by simpa using lt⟩)
    have represented : (BoxPullWeakening.ReverseComponents.tensorRight (copies A m) (copies B n)).ports
        (.input ⟨i.val-m,by simpa using lt⟩) = .input ⟨i.val,by have := i.isLt; simpa using this⟩ := by
      exact congrArg Port.input (Fin.ext (by change (List.replicate m Wire.term).length+(i.val-m)=i.val; simp; omega))
    rw [represented] at eq
    change (remainingSmall A B m n).ports (.input i) =
      (smallBlock A B m (n+1)).ports ((tail B n).ports (.input _)) at eq
    rw [eq,tail_input,smallBlock_input]
    exact congrArg Port.input (Fin.ext (by simp only [ite_eq_right h]; omega))

/-- All remaining private-output blocks shift by the selected large block's
output count, including the zero-output family. -/
theorem remainingLarge_output (m n : Nat) (i : Fin (List.replicate (k*(m+n)) Wire.term).length) :
    (remainingLarge A B m n).ports (.output i) = .output ⟨k+i.val,by
      have := i.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩ := by
  by_cases h : i.val < k*m
  · have eq := Occurrence.tensorJoin_left (largeTail A B m n) (smallBlock A B (m+1) n)
      (largeTail_disjoint A B m n) (.output ⟨i.val,by simpa using h⟩)
    change (remainingLarge A B m n).ports (.output i) =
      (largeBlock A B (m+1) n).ports ((tail A m).ports (.output _)) at eq
    rw [eq,tail_output,largeBlock_output]
  · have lt : i.val-k*m<k*n := by have := i.isLt; simp only [List.length_replicate,Nat.mul_add] at this; omega
    have eq := Occurrence.tensorJoin_right (largeTail A B m n) (smallBlock A B (m+1) n)
      (largeTail_disjoint A B m n) (.output ⟨i.val-k*m,by simpa using lt⟩)
    have represented : (BoxPullWeakening.ReverseComponents.tensorRight (copies A m) (copies B n)).ports
        (.output ⟨i.val-k*m,by simpa using lt⟩) = .output ⟨i.val,by have := i.isLt; simpa [Nat.mul_add] using this⟩ := by
      exact congrArg Port.output (Fin.ext (by change (List.replicate (k*m) Wire.term).length+(i.val-k*m)=i.val; simp; omega))
    rw [represented] at eq
    change (remainingLarge A B m n).ports (.output i) = _ at eq
    rw [eq,smallBlock_output]
    exact congrArg Port.output (Fin.ext (by simp only [Nat.mul_succ]; omega))

/-- Only the small private-output block moves past the selected small member.
For one-output lambdas this is precisely the input permutation above. -/
theorem remainingSmall_output (m n : Nat) (i : Fin (List.replicate (k*(m+n)) Wire.term).length) :
    (remainingSmall A B m n).ports (.output i) =
      .output ⟨if i.val<k*m then i.val else k+i.val,by
        have := i.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; split <;> omega⟩ := by
  by_cases h : i.val < k*m
  · have eq := Occurrence.tensorJoin_left (largeBlock A B m (n+1)) (smallTail A B m n)
      (smallTail_disjoint A B m n) (.output ⟨i.val,by simpa using h⟩)
    change (remainingSmall A B m n).ports (.output i) = _ at eq
    rw [eq,largeBlock_output]
    exact congrArg Port.output (Fin.ext (by simp [h]))
  · have lt : i.val-k*m<k*n := by have := i.isLt; simp only [List.length_replicate,Nat.mul_add] at this; omega
    have eq := Occurrence.tensorJoin_right (largeBlock A B m (n+1)) (smallTail A B m n)
      (smallTail_disjoint A B m n) (.output ⟨i.val-k*m,by simpa using lt⟩)
    have represented : (BoxPullWeakening.ReverseComponents.tensorRight (copies A m) (copies B n)).ports
        (.output ⟨i.val-k*m,by simpa using lt⟩) = .output ⟨i.val,by have := i.isLt; simpa [Nat.mul_add] using this⟩ := by
      exact congrArg Port.output (Fin.ext (by change (List.replicate (k*m) Wire.term).length+(i.val-k*m)=i.val; simp; omega))
    rw [represented] at eq
    change (remainingSmall A B m n).ports (.output i) =
      (smallBlock A B m (n+1)).ports ((tail B n).ports (.output _)) at eq
    rw [eq,tail_output,smallBlock_output]
    exact congrArg Port.output (Fin.ext (by simp only [ite_eq_right h]; omega))

/-- The selected large abstraction occupies the original first input. -/
theorem isolateLarge_first_input (m n : Nat) :
    (isolateLargeIso A B m n).ports.toFun (.input ⟨0,by simp⟩) = .input ⟨0,by simp; omega⟩ := by
  change (isolateLarge A B m n).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft A (family A B m n)).ports (.input 0)) = _
  rw [isolateLarge,Occurrence.tensorJoin_left,large_input]

/-- The selected small abstraction is the original input after all large ones. -/
theorem isolateSmall_first_input (m n : Nat) :
    (isolateSmallIso A B m n).ports.toFun (.input ⟨0,by simp⟩) = .input ⟨m,by simp⟩ := by
  change (isolateSmall A B m n).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft B (family A B m n)).ports (.input 0)) = _
  rw [isolateSmall,Occurrence.tensorJoin_left,small_input]
  rfl

/-- Every other isolated-large input retains its original ordered index. -/
theorem isolateLarge_rest_input (m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (isolateLargeIso A B m n).ports.toFun (.input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
  have eq := Occurrence.tensorJoin_right (large A B (m+1) n ⟨0,by omega⟩)
    (remainingLarge A B m n) (firstLarge_disjoint A B m n) (.input i)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight A (family A B m n)).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))
  rw [represented] at eq
  exact eq.trans (remainingLarge_input A B m n i)

/-- The selected-small rotation shifts large positions back one and leaves
later small positions unchanged. -/
theorem isolateSmall_rest_input (m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (isolateSmallIso A B m n).ports.toFun (.input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩) =
      .input ⟨if i.val<m then i.val else i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; split <;> omega⟩ := by
  have eq := Occurrence.tensorJoin_right (small A B m (n+1) ⟨0,by omega⟩)
    (remainingSmall A B m n) (firstSmall_disjoint A B m n) (.input i)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight B (family A B m n)).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))
  rw [represented] at eq
  exact eq.trans (remainingSmall_input A B m n i)

/-- Outputs of the first large member remain at the first original output block. -/
theorem isolateLarge_first_output (m n : Nat) (i : Fin (List.replicate k Wire.term).length) :
    (isolateLargeIso A B m n).ports.toFun (.output ⟨i.val,by have := i.isLt; simp at *; omega⟩) =
      .output ⟨i.val,by have := i.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩ := by
  have eq := Occurrence.tensorJoin_left (large A B (m+1) n ⟨0,by omega⟩)
    (remainingLarge A B m n) (firstLarge_disjoint A B m n) (.output i)
  exact eq.trans (by rw [large_output]; exact congrArg Port.output (Fin.ext (by simp)))

/-- The selected small output block follows precisely the original large block. -/
theorem isolateSmall_first_output (m n : Nat) (i : Fin (List.replicate k Wire.term).length) :
    (isolateSmallIso A B m n).ports.toFun (.output ⟨i.val,by have := i.isLt; simp at *; omega⟩) =
      .output ⟨k*m+i.val,by have := i.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩ := by
  have eq := Occurrence.tensorJoin_left (small A B m (n+1) ⟨0,by omega⟩)
    (remainingSmall A B m n) (firstSmall_disjoint A B m n) (.output i)
  exact eq.trans (by rw [small_output]; exact congrArg Port.output (Fin.ext (by simp)))

/-- The remaining outputs under large isolation keep their original indices. -/
theorem isolateLarge_rest_output (m n : Nat) (i : Fin (List.replicate (k*(m+n)) Wire.term).length) :
    (isolateLargeIso A B m n).ports.toFun (.output ⟨k+i.val,by have := i.isLt; simp at *; omega⟩) =
      .output ⟨k+i.val,by have := i.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩ := by
  have eq := Occurrence.tensorJoin_right (large A B (m+1) n ⟨0,by omega⟩)
    (remainingLarge A B m n) (firstLarge_disjoint A B m n) (.output i)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight A (family A B m n)).ports (.output i) =
      .output ⟨k+i.val,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.output (Fin.ext (by change (List.replicate k Wire.term).length+i.val=k+i.val; simp))
  rw [represented] at eq
  exact eq.trans (remainingLarge_output A B m n i)

/-- The remaining small-isolation outputs follow the same block rotation as
inputs, with arbitrary output multiplicity k and its zero-output case. -/
theorem isolateSmall_rest_output (m n : Nat) (i : Fin (List.replicate (k*(m+n)) Wire.term).length) :
    (isolateSmallIso A B m n).ports.toFun (.output ⟨k+i.val,by have := i.isLt; simp at *; omega⟩) =
      .output ⟨if i.val<k*m then i.val else k+i.val,by
        have := i.isLt
        simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; split <;> omega⟩ := by
  have eq := Occurrence.tensorJoin_right (small A B m (n+1) ⟨0,by omega⟩)
    (remainingSmall A B m n) (firstSmall_disjoint A B m n) (.output i)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight B (family A B m n)).ports (.output i) =
      .output ⟨k+i.val,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.output (Fin.ext (by change (List.replicate k Wire.term).length+i.val=k+i.val; simp))
  rw [represented] at eq
  exact eq.trans (remainingSmall_output A B m n i)

end Hypernets.Copying.Parametricity.FamilyComponents
