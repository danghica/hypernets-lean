import Hypernets.Copying.ParametricityLiteralReindex

/-! Isolate any original large or small abstraction, with the other members
kept in their original relative block order. All external and private-output
permutations are recorded by genuine recursive boundary isomorphisms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyLiteral
open Graph FamilyComponents

/-- Move the selected original member to position zero in the source order;
the target action inserts it back at its actual original index. -/
def front {n : Nat} (selected : Fin (n+1)) : Bijection (Fin (n+1)) (Fin (n+1)) where
  toFun i := if zero : i.val=0 then selected
    else if before : i.val ≤ selected.val then ⟨i.val-1,by omega⟩ else i
  invFun i := if same : i.val=selected.val then ⟨0,by omega⟩
    else if before : i.val<selected.val then ⟨i.val+1,by have := selected.isLt; omega⟩ else i
  left_inv i := by
    apply Fin.ext
    split <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega
  right_inv i := by
    apply Fin.ext
    split <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;> omega

/-- The first isolated member is exactly the chosen original member. -/
theorem front_zero {n} (selected : Fin (n+1)) : (front selected).toFun ⟨0,by omega⟩ = selected := rfl

/-- Every remaining member retains its original order after deleting the
selected index; no swap of two unrelated remaining members is hidden. -/
theorem front_rest {n} (selected : Fin (n+1)) (i : Fin n) :
    ((front selected).toFun ⟨i.val+1,by omega⟩).val =
      if i.val < selected.val then i.val else i.val+1 := by
  simp only [front,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceDIte]
  split <;> split <;> simp_all <;> omega

/-- Isolate any selected large member of the original left family. -/
noncomputable def leftLargeAt (d m n : Nat) (selected : Fin (m+1)) :
    BoundaryIso (Net.Tensor.net (largeLeft d) (leftFamily d m n)) (leftFamily d (m+1) n) :=
  (leftLarge d m n).trans (leftReindex d (front selected) (Bijection.refl _))

/-- The corresponding right isolation uses the identical selected index. -/
noncomputable def rightLargeAt (d m n : Nat) (selected : Fin (m+1)) :
    BoundaryIso (Net.Tensor.net (largeRight d) (rightFamily d m n)) (rightFamily d (m+1) n) :=
  (rightLarge d m n).trans (rightReindex d (front selected) (Bijection.refl _))

/-- Isolate any selected small member, preserving all other large and small
members in their original relative order. -/
noncomputable def leftSmallAt (d m n : Nat) (selected : Fin (n+1)) :
    BoundaryIso (Net.Tensor.net (smallLeft (d+1)) (leftFamily d m n)) (leftFamily d m (n+1)) :=
  (leftSmall d m n).trans (leftReindex d (Bijection.refl _) (front selected))

/-- The complete original right small family has the same boundary action. -/
noncomputable def rightSmallAt (d m n : Nat) (selected : Fin (n+1)) :
    BoundaryIso (Net.Tensor.net (smallRight (d+1)) (rightFamily d m n)) (rightFamily d m (n+1)) :=
  (rightSmall d m n).trans (rightReindex d (Bijection.refl _) (front selected))

/-- Arbitrary-large isolation synchronizes both inputs and private outputs. -/
theorem largeAt_synchronous (d m n : Nat) (selected : Fin (m+1)) :
    BoundaryIso.Synchronous (leftLargeAt d m n selected) (rightLargeAt d m n selected) :=
  (show BoundaryIso.Synchronous (leftLarge d m n) (rightLarge d m n) from
    ⟨large_inputs d m n,large_private d m n⟩).trans (reindex_synchronous d (front selected) (Bijection.refl _))

/-- Arbitrary-small isolation synchronizes both inputs and private outputs. -/
theorem smallAt_synchronous (d m n : Nat) (selected : Fin (n+1)) :
    BoundaryIso.Synchronous (leftSmallAt d m n selected) (rightSmallAt d m n selected) :=
  (show BoundaryIso.Synchronous (leftSmall d m n) (rightSmall d m n) from
    ⟨small_inputs d m n,small_private d m n⟩).trans (reindex_synchronous d (Bijection.refl _) (front selected))

/-- The actual isolated large input maps to the chosen original large index. -/
theorem leftLargeAt_first_input (d m n : Nat) (selected : Fin (m+1)) :
    (leftLargeAt d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨selected.val,by simp; have := selected.isLt; omega⟩ := by
  change (leftReindex d (front selected) (Bijection.refl _)).ports.toFun
    ((leftLarge d m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [leftLarge_first_input,leftReindex_input]
  simp only [blockIndex,Nat.zero_lt_succ,↓reduceDIte,front_zero]

/-- The actual isolated right large input has exactly the same attachment. -/
theorem rightLargeAt_first_input (d m n : Nat) (selected : Fin (m+1)) :
    (rightLargeAt d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨selected.val,by simp; have := selected.isLt; omega⟩ := by
  change (rightReindex d (front selected) (Bijection.refl _)).ports.toFun
    ((rightLarge d m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [rightLarge_first_input,rightReindex_input]
  simp only [blockIndex,Nat.zero_lt_succ,↓reduceDIte,front_zero]

/-- The small selected entry is its actual index after the unchanged large block. -/
theorem leftSmallAt_first_input (d m n : Nat) (selected : Fin (n+1)) :
    (leftSmallAt d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨m+selected.val,by simp⟩ := by
  change (leftReindex d (Bijection.refl _) (front selected)).ports.toFun
    ((leftSmall d m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [leftSmall_first_input,leftReindex_input]
  simp only [blockIndex,Nat.lt_irrefl,↓reduceDIte,Nat.sub_self,front_zero]

/-- The actual right small entry has the identical original block offset. -/
theorem rightSmallAt_first_input (d m n : Nat) (selected : Fin (n+1)) :
    (rightSmallAt d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨m+selected.val,by simp⟩ := by
  change (rightReindex d (Bijection.refl _) (front selected)).ports.toFun
    ((rightSmall d m n).ports.toFun (.input ⟨0,by simp⟩)) = _
  rw [rightSmall_first_input,rightReindex_input]
  simp only [blockIndex,Nat.lt_irrefl,↓reduceDIte,Nat.sub_self,front_zero]

end Hypernets.Copying.Parametricity.FamilyLiteral
