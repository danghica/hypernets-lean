import Hypernets.Copying.ParametricityFamilyReindex
import Hypernets.Copying.ParametricityFamilyBoundary
import Hypernets.Copying.BoundarySynchrony

/-! Simultaneous reindexing of the literal left and right Figure20 families.
Both sides share the full input action, and the private output action agrees. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyLiteral
open Graph FamilyComponents
variable (d : Nat) {m n : Nat} (p : Bijection (Fin m) (Fin m)) (q : Bijection (Fin n) (Fin n))

/-- The actual left family with independently reordered complete blocks. -/
noncomputable def leftReindex : BoundaryIso (leftFamily d m n) (leftFamily d m n) :=
  (leftIso d m n).symm.trans
    ((reindexFamily (k := 1) (largeLeft d) (smallLeft (d+1)) p q).trans (leftIso d m n))

/-- The actual right family has the identical selected member ordering. -/
noncomputable def rightReindex : BoundaryIso (rightFamily d m n) (rightFamily d m n) :=
  (rightIso d m n).symm.trans
    ((reindexFamily (k := 0) (largeRight d) (smallRight (d+1)) p q).trans (rightIso d m n))

/-- Exact external action on the original left ordered inputs. -/
theorem leftReindex_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftReindex d p q).ports.toFun (.input i) =
      .input ⟨(blockIndex p q ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ := by
  change (leftIso d m n).ports.toFun ((reindexFamily (k := 1) (largeLeft d) (smallLeft (d+1)) p q).ports.toFun
    ((leftIso d m n).ports.invFun (.input i))) = _
  rw [left_inv_input,reindexFamily_input,left_input]

/-- Exact external action on the original right ordered inputs. -/
theorem rightReindex_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (rightReindex d p q).ports.toFun (.input i) =
      .input ⟨(blockIndex p q ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ := by
  change (rightIso d m n).ports.toFun ((reindexFamily (k := 0) (largeRight d) (smallRight (d+1)) p q).ports.toFun
    ((rightIso d m n).ports.invFun (.input i))) = _
  rw [right_inv_input,reindexFamily_input,right_input]

/-- Every private left output follows its original lambda input. -/
theorem leftReindex_output (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftReindex d p q).ports.toFun (.output i) =
      .output ⟨(blockIndex p q ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ := by
  change (leftIso d m n).ports.toFun ((reindexFamily (k := 1) (largeLeft d) (smallLeft (d+1)) p q).ports.toFun
    ((leftIso d m n).ports.invFun (.output i))) = _
  rw [left_inv_output,reindexFamily_output_one,left_output]

/-- Reindexing is synchronous on both original family inputs and private outputs. -/
theorem reindex_synchronous : BoundaryIso.Synchronous (leftReindex d p q) (rightReindex d p q) := by
  constructor
  · intro i
    have l := (leftReindex d p q).map_input i
    have r := (rightReindex d p q).map_input i
    rw [leftReindex_input] at l
    rw [rightReindex_input] at r
    exact (Port.input.inj l).symm.trans (Port.input.inj r)
  · intro i
    have l := (leftReindex d p q).map_input i
    have r := (leftReindex d p q).map_output i
    rw [leftReindex_input] at l
    rw [leftReindex_output] at r
    exact (Port.output.inj r).symm.trans (Port.input.inj l)

end Hypernets.Copying.Parametricity.FamilyLiteral
