import Hypernets.Copying.ParametricityFamilyLiteralCoordinates

/-! Coincidence of the left private-output permutation and the two external
input permutations is proved from the literal component coordinates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyLiteral
open Graph

/-- The first-small cyclic move, as an explicit numerical coordinate map. -/
def smallIndex (m i : Nat) : Nat := if i=0 then m else if i-1<m then i-1 else i

/-- The whole ordered left input action of first-large isolation. -/
theorem leftLarge_inputs_val (d m n : Nat)
    (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    ((leftLarge d m n).inputs.toFun i).val = i.val := by
  change ((leftLarge d m n).inputMap i).val = _
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have h := (leftLarge d m n).map_input ⟨0,by simp⟩
    rw [leftLarge_first_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    exact value.symm
  · let j : Fin (List.replicate (m+n) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at *; omega⟩
    have eq : i = ⟨1+j.val,by have := j.isLt; simp at *; omega⟩ := by
      apply Fin.ext; dsimp [j]; omega
    have h := (leftLarge d m n).map_input i
    rw [eq,leftLarge_rest_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    rw [← eq] at value
    dsimp [j] at value
    omega

/-- The whole ordered right input action of first-large isolation. -/
theorem rightLarge_inputs_val (d m n : Nat)
    (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    ((rightLarge d m n).inputs.toFun i).val = i.val := by
  change ((rightLarge d m n).inputMap i).val = _
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have h := (rightLarge d m n).map_input ⟨0,by simp⟩
    rw [rightLarge_first_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    exact value.symm
  · let j : Fin (List.replicate (m+n) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at *; omega⟩
    have eq : i = ⟨1+j.val,by have := j.isLt; simp at *; omega⟩ := by
      apply Fin.ext; dsimp [j]; omega
    have h := (rightLarge d m n).map_input i
    rw [eq,rightLarge_rest_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    rw [← eq] at value
    dsimp [j] at value
    omega

/-- The whole ordered left output action of first-large isolation. -/
theorem leftLarge_outputs_val (d m n : Nat)
    (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    ((leftLarge d m n).outputs.toFun i).val = i.val := by
  change ((leftLarge d m n).outputMap i).val = _
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have h := (leftLarge d m n).map_output ⟨0,by simp⟩
    rw [leftLarge_first_output] at h
    have value := congrArg Fin.val (Port.output.inj h)
    exact value.symm
  · let j : Fin (List.replicate (m+n) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at *; omega⟩
    have eq : i = ⟨1+j.val,by have := j.isLt; simp at *; omega⟩ := by
      apply Fin.ext; dsimp [j]; omega
    have h := (leftLarge d m n).map_output i
    rw [eq,leftLarge_rest_output] at h
    have value := congrArg Fin.val (Port.output.inj h)
    rw [← eq] at value
    dsimp [j] at value
    omega

/-- The whole ordered left input action of first-small isolation. -/
theorem leftSmall_inputs_val (d m n : Nat)
    (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    ((leftSmall d m n).inputs.toFun i).val = smallIndex m i.val := by
  change ((leftSmall d m n).inputMap i).val = _
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have h := (leftSmall d m n).map_input ⟨0,by simp⟩
    rw [leftSmall_first_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    simpa [smallIndex] using value.symm
  · let j : Fin (List.replicate (m+n) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at *; omega⟩
    have eq : i = ⟨1+j.val,by have := j.isLt; simp at *; omega⟩ := by
      apply Fin.ext; dsimp [j]; omega
    have h := (leftSmall d m n).map_input i
    rw [eq,leftSmall_rest_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    rw [← eq] at value
    have successor : j.val+1=i.val := by dsimp [j]; omega
    simpa [smallIndex,zero,successor,j] using value.symm

/-- The whole ordered right input action of first-small isolation. -/
theorem rightSmall_inputs_val (d m n : Nat)
    (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    ((rightSmall d m n).inputs.toFun i).val = smallIndex m i.val := by
  change ((rightSmall d m n).inputMap i).val = _
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have h := (rightSmall d m n).map_input ⟨0,by simp⟩
    rw [rightSmall_first_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    simpa [smallIndex] using value.symm
  · let j : Fin (List.replicate (m+n) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at *; omega⟩
    have eq : i = ⟨1+j.val,by have := j.isLt; simp at *; omega⟩ := by
      apply Fin.ext; dsimp [j]; omega
    have h := (rightSmall d m n).map_input i
    rw [eq,rightSmall_rest_input] at h
    have value := congrArg Fin.val (Port.input.inj h)
    rw [← eq] at value
    have successor : j.val+1=i.val := by dsimp [j]; omega
    simpa [smallIndex,zero,successor,j] using value.symm

/-- The whole ordered left output action of first-small isolation. -/
theorem leftSmall_outputs_val (d m n : Nat)
    (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    ((leftSmall d m n).outputs.toFun i).val = smallIndex m i.val := by
  change ((leftSmall d m n).outputMap i).val = _
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have h := (leftSmall d m n).map_output ⟨0,by simp⟩
    rw [leftSmall_first_output] at h
    have value := congrArg Fin.val (Port.output.inj h)
    simpa [smallIndex] using value.symm
  · let j : Fin (List.replicate (m+n) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] at *; omega⟩
    have eq : i = ⟨1+j.val,by have := j.isLt; simp at *; omega⟩ := by
      apply Fin.ext; dsimp [j]; omega
    have h := (leftSmall d m n).map_output i
    rw [eq,leftSmall_rest_output] at h
    have value := congrArg Fin.val (Port.output.inj h)
    rw [← eq] at value
    have successor : j.val+1=i.val := by dsimp [j]; omega
    simpa [smallIndex,zero,successor,j] using value.symm

/-- Both sides of Figure20 perform the same external input permutation. -/
theorem large_inputs (d m n : Nat) (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    (leftLarge d m n).inputs.toFun i = (rightLarge d m n).inputs.toFun i := by
  apply Fin.ext
  rw [leftLarge_inputs_val,rightLarge_inputs_val]

/-- The private sharing-tree attachment follows the input permutation exactly. -/
theorem large_private (d m n : Nat) (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    (leftLarge d m n).outputs.toFun i = (leftLarge d m n).inputs.toFun i := by
  apply Fin.ext
  rw [leftLarge_outputs_val,leftLarge_inputs_val]

/-- Both sides of Figure20 perform the same external input permutation. -/
theorem small_inputs (d m n : Nat) (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    (leftSmall d m n).inputs.toFun i = (rightSmall d m n).inputs.toFun i := by
  apply Fin.ext
  rw [leftSmall_inputs_val,rightSmall_inputs_val]

/-- The private sharing-tree attachment follows the input permutation exactly. -/
theorem small_private (d m n : Nat) (i : Fin ([Wire.term] ++ List.replicate (m+n) Wire.term).length) :
    (leftSmall d m n).outputs.toFun i = (leftSmall d m n).inputs.toFun i := by
  apply Fin.ext
  rw [leftSmall_outputs_val,leftSmall_inputs_val]

end Hypernets.Copying.Parametricity.FamilyLiteral
