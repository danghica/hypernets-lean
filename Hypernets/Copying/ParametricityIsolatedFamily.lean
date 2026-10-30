import Hypernets.Copying.ParametricityFamilyBoundary
import Hypernets.Copying.BoundarySourceReboundary
import Hypernets.Copying.ParametricityBoundaryWitness

/-! Genuine original parametricity specimens with one selected abstraction
first, preserving the complete remaining ordered family and private tree. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.IsolatedFamily
open Graph

/-- Only equal-list presentations are exposed; the selected small lambda
and every remaining original lambda are unchanged. -/
def smallLeftFamily (d m n : Nat) :
    Hypernet (d+2) (List.replicate ((m+n)+1) .term) (List.replicate ((m+n)+1) .term) :=
  (Net.Tensor.net (smallLeft (d+1)) (leftFamily d m n)).reboundary
    (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

def smallRightFamily (d m n : Nat) :
    Hypernet (d+2) (List.replicate ((m+n)+1) .term) [] :=
  (Net.Tensor.net (smallRight (d+1)) (rightFamily d m n)).reboundary
    (by simp [List.replicate_succ]) rfl

noncomputable def smallLeftIso (d m n : Nat) :
    BoundaryIso (smallLeftFamily d m n) (leftFamily d m (n+1)) :=
  (FamilyLiteral.leftSmall d m n).reboundarySource _ _

noncomputable def smallRightIso (d m n : Nat) :
    BoundaryIso (smallRightFamily d m n) (rightFamily d m (n+1)) :=
  (FamilyLiteral.rightSmall d m n).reboundarySource _ _

theorem small_same_inputs (d m n : Nat) (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (smallLeftIso d m n).inputs.toFun i = (smallRightIso d m n).inputs.toFun i := by
  rw [smallLeftIso,smallRightIso,BoundaryIso.reboundarySource_inputs,BoundaryIso.reboundarySource_inputs]
  exact FamilyLiteral.small_inputs d m n _

/-- An arbitrary original private sharing tree attaches to all selected and
remaining free x outputs, in their explicitly isolated order. -/
def smallClosed {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1)) :
    Hypernet (d+2) (List.replicate ((m+n)+1) .term) [] :=
  Serial.net (Serial.net (smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))

/-- This is an actual original-template filling, obtained by placing the
literal family in a common input permutation context and reindexing C. -/
noncomputable def smallWitness {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1)) :
    FillingWitness template (smallClosed d C) (smallRightFamily d m n) :=
  BoundaryWitness.filling_reboundary_tree (by omega) (by congr 1)
    (smallLeftIso d m n) (smallRightIso d m n) C (small_same_inputs d m n)

/-- Only equal-list presentations are exposed; the selected large lambda
and every remaining original lambda are unchanged. -/
def largeLeftFamily (d m n : Nat) :
    Hypernet (d+2) (List.replicate ((m+n)+1) .term) (List.replicate ((m+n)+1) .term) :=
  (Net.Tensor.net (largeLeft d) (leftFamily d m n)).reboundary
    (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

def largeRightFamily (d m n : Nat) :
    Hypernet (d+2) (List.replicate ((m+n)+1) .term) [] :=
  (Net.Tensor.net (largeRight d) (rightFamily d m n)).reboundary
    (by simp [List.replicate_succ]) rfl

noncomputable def largeLeftIso (d m n : Nat) :
    BoundaryIso (largeLeftFamily d m n) (leftFamily d (m+1) n) :=
  (FamilyLiteral.leftLarge d m n).reboundarySource _ _

noncomputable def largeRightIso (d m n : Nat) :
    BoundaryIso (largeRightFamily d m n) (rightFamily d (m+1) n) :=
  (FamilyLiteral.rightLarge d m n).reboundarySource _ _

theorem large_same_inputs (d m n : Nat) (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (largeLeftIso d m n).inputs.toFun i = (largeRightIso d m n).inputs.toFun i := by
  rw [largeLeftIso,largeRightIso,BoundaryIso.reboundarySource_inputs,BoundaryIso.reboundarySource_inputs]
  exact FamilyLiteral.large_inputs d m n _

/-- An arbitrary original private sharing tree attaches to all selected and
remaining free x outputs, in their explicitly isolated order. -/
def largeClosed {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1)) :
    Hypernet (d+2) (List.replicate ((m+n)+1) .term) [] :=
  Serial.net (Serial.net (largeLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))

/-- This is an actual original-template filling, obtained by placing the
literal family in a common input permutation context and reindexing C. -/
noncomputable def largeWitness {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1)) :
    FillingWitness template (largeClosed d C) (largeRightFamily d m n) :=
  BoundaryWitness.filling_reboundary_tree (by omega) (by congr 1; omega)
    (largeLeftIso d m n) (largeRightIso d m n) C (large_same_inputs d m n)

end Hypernets.Copying.Parametricity.IsolatedFamily
