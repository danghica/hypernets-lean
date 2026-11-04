import Hypernets.Copying.ParametricitySelectedFamily
import Hypernets.Copying.ParametricityIsolatedFamily

/-! Arbitrary selected members in the exact equal-list presentations used
by the checked first-entry application and copying diagrams. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.IsolatedFamily
open Graph

/-- The canonical isolated left family identifies any original large member. -/
noncomputable def largeLeftAtIso (d m n : Nat) (selected : Fin (m+1)) :
    BoundaryIso (largeLeftFamily d m n) (leftFamily d (m+1) n) :=
  (FamilyLiteral.leftLargeAt d m n selected).reboundarySource _ _

/-- The right canonical family identifies the same original large member. -/
noncomputable def largeRightAtIso (d m n : Nat) (selected : Fin (m+1)) :
    BoundaryIso (largeRightFamily d m n) (rightFamily d (m+1) n) :=
  (FamilyLiteral.rightLargeAt d m n selected).reboundarySource _ _

/-- The canonical isolated left family identifies any original small member. -/
noncomputable def smallLeftAtIso (d m n : Nat) (selected : Fin (n+1)) :
    BoundaryIso (smallLeftFamily d m n) (leftFamily d m (n+1)) :=
  (FamilyLiteral.leftSmallAt d m n selected).reboundarySource _ _

/-- The right canonical family identifies the same original small member. -/
noncomputable def smallRightAtIso (d m n : Nat) (selected : Fin (n+1)) :
    BoundaryIso (smallRightFamily d m n) (rightFamily d m (n+1)) :=
  (FamilyLiteral.rightSmallAt d m n selected).reboundarySource _ _

/-- Exact common input action for any originally selected large member. -/
theorem largeAt_same_inputs (d m n : Nat) (selected : Fin (m+1))
    (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (largeLeftAtIso d m n selected).inputs.toFun i = (largeRightAtIso d m n selected).inputs.toFun i := by
  rw [largeLeftAtIso,largeRightAtIso,BoundaryIso.reboundarySource_inputs,BoundaryIso.reboundarySource_inputs]
  exact (FamilyLiteral.largeAt_synchronous d m n selected).1 _

/-- Exact common input action for any originally selected small member. -/
theorem smallAt_same_inputs (d m n : Nat) (selected : Fin (n+1))
    (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (smallLeftAtIso d m n selected).inputs.toFun i = (smallRightAtIso d m n selected).inputs.toFun i := by
  rw [smallLeftAtIso,smallRightAtIso,BoundaryIso.reboundarySource_inputs,BoundaryIso.reboundarySource_inputs]
  exact (FamilyLiteral.smallAt_synchronous d m n selected).1 _

/-- The large private attachment agrees with the complete input action. -/
theorem largeAt_private (d m n : Nat) (selected : Fin (m+1))
    (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (largeLeftAtIso d m n selected).outputs.toFun i = (largeLeftAtIso d m n selected).inputs.toFun i := by
  rw [largeLeftAtIso,BoundaryIso.reboundarySource_outputs,BoundaryIso.reboundarySource_inputs]
  exact (FamilyLiteral.largeAt_synchronous d m n selected).2 _

/-- The small private attachment agrees with the complete input action. -/
theorem smallAt_private (d m n : Nat) (selected : Fin (n+1))
    (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (smallLeftAtIso d m n selected).outputs.toFun i = (smallLeftAtIso d m n selected).inputs.toFun i := by
  rw [smallLeftAtIso,BoundaryIso.reboundarySource_outputs,BoundaryIso.reboundarySource_inputs]
  exact (FamilyLiteral.smallAt_synchronous d m n selected).2 _

/-- The literal canonical first input denotes the chosen original large entry. -/
theorem largeLeftAtIso_first (d m n : Nat) (selected : Fin (m+1)) :
    (largeLeftAtIso d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨selected.val,by simp; have := selected.isLt; omega⟩ := by
  change (FamilyLiteral.leftLargeAt d m n selected).ports.toFun
    ((BoundaryIso.interfaceEquality _ _ _).ports.invFun (.input ⟨0,by simp⟩)) = _
  rw [BoundaryIso.interfaceEquality_inverse]
  exact FamilyLiteral.leftLargeAt_first_input d m n selected

/-- The right canonical first input has the identical original large index. -/
theorem largeRightAtIso_first (d m n : Nat) (selected : Fin (m+1)) :
    (largeRightAtIso d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨selected.val,by simp; have := selected.isLt; omega⟩ := by
  change (FamilyLiteral.rightLargeAt d m n selected).ports.toFun
    ((BoundaryIso.interfaceEquality _ _ _).ports.invFun (.input ⟨0,by simp⟩)) = _
  rw [BoundaryIso.interfaceEquality_inverse]
  exact FamilyLiteral.rightLargeAt_first_input d m n selected

/-- The canonical small entry denotes its original offset after the large block. -/
theorem smallLeftAtIso_first (d m n : Nat) (selected : Fin (n+1)) :
    (smallLeftAtIso d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨m+selected.val,by simp⟩ := by
  change (FamilyLiteral.leftSmallAt d m n selected).ports.toFun
    ((BoundaryIso.interfaceEquality _ _ _).ports.invFun (.input ⟨0,by simp⟩)) = _
  rw [BoundaryIso.interfaceEquality_inverse]
  exact FamilyLiteral.leftSmallAt_first_input d m n selected

/-- The right canonical small entry has the identical original block offset. -/
theorem smallRightAtIso_first (d m n : Nat) (selected : Fin (n+1)) :
    (smallRightAtIso d m n selected).ports.toFun (.input ⟨0,by simp⟩) =
      .input ⟨m+selected.val,by simp⟩ := by
  change (FamilyLiteral.rightSmallAt d m n selected).ports.toFun
    ((BoundaryIso.interfaceEquality _ _ _).ports.invFun (.input ⟨0,by simp⟩)) = _
  rw [BoundaryIso.interfaceEquality_inverse]
  exact FamilyLiteral.rightSmallAt_first_input d m n selected

end Hypernets.Copying.Parametricity.IsolatedFamily
