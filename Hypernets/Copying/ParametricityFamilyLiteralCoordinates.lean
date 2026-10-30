import Hypernets.Copying.ParametricityFamilyLiteral
import Hypernets.Copying.BoundaryTensorPorts

/-! Literal Figure20 isolation keeps the exact selected and remaining
external coordinates; left private outputs undergo the same permutation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyLiteral
open Graph Opening FamilyComponents

/-- First-large isolation fixes the selected original input. -/
theorem leftLarge_first_input (d m n : Nat) :
    (leftLarge d m n).ports.toFun (.input ⟨0,by simp⟩) = .input ⟨0,by simp; omega⟩ := by
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) (leftFamily d m n)).ports (.input 0)))) = _
  rw [BoundaryIso.tensor_left_port]
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [isolateLarge_first_input,left_input]

/-- Right isolation fixes the very same selected first-large input. -/
theorem rightLarge_first_input (d m n : Nat) :
    (rightLarge d m n).ports.toFun (.input ⟨0,by simp⟩) = .input ⟨0,by simp; omega⟩ := by
  change (rightIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (rightIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorLeft (largeRight d) (rightFamily d m n)).ports (.input 0)))) = _
  rw [BoundaryIso.tensor_left_port]
  change (rightIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [isolateLarge_first_input,right_input]

/-- First-small left isolation selects precisely the original index m. -/
theorem leftSmall_first_input (d m n : Nat) :
    (leftSmall d m n).ports.toFun (.input ⟨0,by simp⟩) = .input ⟨m,by simp⟩ := by
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m n)).ports (.input 0)))) = _
  rw [BoundaryIso.tensor_left_port]
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [isolateSmall_first_input,left_input]

/-- First-small right isolation selects that same original index. -/
theorem rightSmall_first_input (d m n : Nat) :
    (rightSmall d m n).ports.toFun (.input ⟨0,by simp⟩) = .input ⟨m,by simp⟩ := by
  change (rightIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (rightIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallRight (d+1)) (rightFamily d m n)).ports (.input 0)))) = _
  rw [BoundaryIso.tensor_left_port]
  change (rightIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [isolateSmall_first_input,right_input]

/-- Remaining large-isolation inputs preserve their original order. -/
theorem leftLarge_rest_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftLarge d m n).ports.toFun (.input ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (leftFamily d m n)).ports (.input i)))) = _
  rw [BoundaryIso.tensor_right_port]
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    ((BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports
      ((leftIso d m n).ports.invFun (.input i)))) = _
  rw [left_inv_input]
  have eq := isolateLarge_rest_input (k := 1) (largeLeft d) (smallLeft (d+1)) m n i
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d)
      (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))
  rw [represented,eq,left_input]

/-- The right family's remaining input map agrees exactly with the left. -/
theorem rightLarge_rest_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (rightLarge d m n).ports.toFun (.input ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
  change (rightIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (rightIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorRight (largeRight d) (rightFamily d m n)).ports (.input i)))) = _
  rw [BoundaryIso.tensor_right_port]
  change (rightIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun
    ((BoxPullWeakening.ReverseComponents.tensorRight (largeRight d) (family (k := 0) (largeRight d) (smallRight (d+1)) m n)).ports
      ((rightIso d m n).ports.invFun (.input i)))) = _
  rw [right_inv_input]
  have eq := isolateLarge_rest_input (k := 0) (largeRight d) (smallRight (d+1)) m n i
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (largeRight d)
      (family (k := 0) (largeRight d) (smallRight (d+1)) m n)).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))
  rw [represented,eq,right_input]

/-- Remaining inputs under first-small isolation retain large-first order
and shift only the original remaining small block. -/
theorem leftSmall_rest_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftSmall d m n).ports.toFun (.input ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) =
      .input ⟨if i.val<m then i.val else i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; split <;> omega⟩ := by
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m n)).ports (.input i)))) = _
  rw [BoundaryIso.tensor_right_port]
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    ((BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports
      ((leftIso d m n).ports.invFun (.input i)))) = _
  rw [left_inv_input]
  have eq := isolateSmall_rest_input (k := 1) (largeLeft d) (smallLeft (d+1)) m n i
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1))
      (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))
  rw [represented,eq,left_input]

/-- Remaining inputs under first-small isolation retain large-first order
and shift only the original remaining small block. -/
theorem rightSmall_rest_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (rightSmall d m n).ports.toFun (.input ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) =
      .input ⟨if i.val<m then i.val else i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; split <;> omega⟩ := by
  change (rightIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (rightIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (rightFamily d m n)).ports (.input i)))) = _
  rw [BoundaryIso.tensor_right_port]
  change (rightIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 0) (largeRight d) (smallRight (d+1)) m n).ports.toFun
    ((BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1)) (family (k := 0) (largeRight d) (smallRight (d+1)) m n)).ports
      ((rightIso d m n).ports.invFun (.input i)))) = _
  rw [right_inv_input]
  have eq := isolateSmall_rest_input (k := 0) (largeRight d) (smallRight (d+1)) m n i
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (smallRight (d+1))
      (family (k := 0) (largeRight d) (smallRight (d+1)) m n)).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))
  rw [represented,eq,right_input]

/-- The selected private output follows the same original coordinate as
its selected term input. -/
theorem leftLarge_first_output (d m n : Nat) :
    (leftLarge d m n).ports.toFun (.output ⟨0,by simp⟩) = .output ⟨0,by simp; omega⟩ := by
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) (leftFamily d m n)).ports (.output 0)))) = _
  rw [BoundaryIso.tensor_left_port]
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun (.output ⟨0,by simp⟩)) = _
  rw [isolateLarge_first_output (k := 1) (largeLeft d) (smallLeft (d+1)) m n ⟨0,by simp⟩,left_output]

/-- The selected private output follows the same original coordinate as
its selected term input. -/
theorem leftSmall_first_output (d m n : Nat) :
    (leftSmall d m n).ports.toFun (.output ⟨0,by simp⟩) = .output ⟨m,by simp⟩ := by
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m n)).ports (.output 0)))) = _
  rw [BoundaryIso.tensor_left_port]
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun (.output ⟨0,by simp⟩)) = _
  rw [isolateSmall_first_output (k := 1) (largeLeft d) (smallLeft (d+1)) m n ⟨0,by simp⟩,left_output]
  exact congrArg Port.output (Fin.ext (by simp))

/-- Every remaining private output has exactly the same ordered action
as the corresponding remaining term input. -/
theorem leftLarge_rest_output (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftLarge d m n).ports.toFun (.output ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) =
      .output ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (leftFamily d m n)).ports (.output i)))) = _
  rw [BoundaryIso.tensor_right_port]
  change (leftIso d (m+1) n).ports.toFun ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    ((BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports
      ((leftIso d m n).ports.invFun (.output i)))) = _
  rw [left_inv_output]
  have eq := isolateLarge_rest_output (k := 1) (largeLeft d) (smallLeft (d+1)) m n ⟨i.val,by simpa using i.isLt⟩
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d)
      (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports (.output ⟨i.val,by simpa using i.isLt⟩) =
      .output ⟨1+i.val,by have := i.isLt; simp at *; omega⟩ := rfl
  rw [represented,eq,left_output]
  exact congrArg Port.output (Fin.ext (by simp [Nat.add_comm]))

/-- Every remaining private output has exactly the same ordered action
as the corresponding remaining term input. -/
theorem leftSmall_rest_output (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftSmall d m n).ports.toFun (.output ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) =
      .output ⟨if i.val<m then i.val else i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; split <;> omega⟩ := by
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    (((BoundaryIso.refl _).tensor (leftIso d m n).symm).ports.toFun
      ((BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m n)).ports (.output i)))) = _
  rw [BoundaryIso.tensor_right_port]
  change (leftIso d m (n+1)).ports.toFun ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).ports.toFun
    ((BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports
      ((leftIso d m n).ports.invFun (.output i)))) = _
  rw [left_inv_output]
  have eq := isolateSmall_rest_output (k := 1) (largeLeft d) (smallLeft (d+1)) m n ⟨i.val,by simpa using i.isLt⟩
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1))
      (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n)).ports (.output ⟨i.val,by simpa using i.isLt⟩) =
      .output ⟨1+i.val,by have := i.isLt; simp at *; omega⟩ := rfl
  rw [represented,eq,left_output]
  exact congrArg Port.output (Fin.ext (by simp [Nat.add_comm]))

end Hypernets.Copying.Parametricity.FamilyLiteral
