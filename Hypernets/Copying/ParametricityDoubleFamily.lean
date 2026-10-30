import Hypernets.Copying.ParametricityFamilyBoundary
import Hypernets.Copying.TensorAssociation
import Hypernets.Copying.BoundarySynchrony

/-! Exact enlarged Figure20 families after duplicating either abstraction.
Both actual copies precede the remaining original family. The simultaneous
input/private-output action is proved, so the private tree can be reindexed
without changing the observational interface. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyLiteral
open Graph

/-- Tensor reassociation has the same boundary action on the two families
and preserves the left private-output/input correspondence. -/
theorem association_synchronous {d I J K}
    (A : Hypernet d I I) (B : Hypernet d J J) (C : Hypernet d K K)
    (A' : Hypernet d I []) (B' : Hypernet d J []) (C' : Hypernet d K []) :
    BoundaryIso.Synchronous (TensorAssociation.iso A B C) (TensorAssociation.iso A' B' C') := by
  constructor
  · intro i
    apply Fin.ext
    have left := (TensorAssociation.iso A B C).map_input i
    have right := (TensorAssociation.iso A' B' C').map_input i
    rw [TensorAssociation.input] at left right
    exact (congrArg Fin.val (Port.input.inj left)).symm.trans (congrArg Fin.val (Port.input.inj right))
  · intro i
    apply Fin.ext
    have out := (TensorAssociation.iso A B C).map_output i
    have inp := (TensorAssociation.iso A B C).map_input i
    rw [TensorAssociation.output] at out
    rw [TensorAssociation.input] at inp
    exact (congrArg Fin.val (Port.output.inj out)).symm.trans (congrArg Fin.val (Port.input.inj inp))

/-- Two actual left large abstractions, in their copy order, are followed by
all original remaining abstractions. No box body is changed. -/
noncomputable def leftLargeDouble (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (Net.Tensor.net (largeLeft d) (largeLeft d)) (leftFamily d m n))
      (leftFamily d (m+2) n) :=
  (TensorAssociation.iso (largeLeft d) (largeLeft d) (leftFamily d m n)).trans
    (((BoundaryIso.refl _).tensor (leftLarge d m n)).trans (leftLarge d (m+1) n))

noncomputable def rightLargeDouble (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (Net.Tensor.net (largeRight d) (largeRight d)) (rightFamily d m n))
      (rightFamily d (m+2) n) :=
  (TensorAssociation.iso (largeRight d) (largeRight d) (rightFamily d m n)).trans
    (((BoundaryIso.refl _).tensor (rightLarge d m n)).trans (rightLarge d (m+1) n))

/-- The two selected small abstractions are moved together past the original
large block, with the same move on their two private outputs. -/
noncomputable def leftSmallDouble (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (Net.Tensor.net (smallLeft (d+1)) (smallLeft (d+1))) (leftFamily d m n))
      (leftFamily d m (n+2)) :=
  (TensorAssociation.iso (smallLeft (d+1)) (smallLeft (d+1)) (leftFamily d m n)).trans
    (((BoundaryIso.refl _).tensor (leftSmall d m n)).trans (leftSmall d m (n+1)))

noncomputable def rightSmallDouble (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (Net.Tensor.net (smallRight (d+1)) (smallRight (d+1))) (rightFamily d m n))
      (rightFamily d m (n+2)) :=
  (TensorAssociation.iso (smallRight (d+1)) (smallRight (d+1)) (rightFamily d m n)).trans
    (((BoundaryIso.refl _).tensor (rightSmall d m n)).trans (rightSmall d m (n+1)))

/-- The enlarged large families have a single common external input action,
which is also the left private-output action. -/
theorem largeDouble_synchronous (d m n : Nat) :
    BoundaryIso.Synchronous (leftLargeDouble d m n) (rightLargeDouble d m n) :=
  (association_synchronous _ _ _ _ _ _).trans
    (((BoundaryIso.synchronous_refl _ _).tensor ⟨large_inputs d m n,large_private d m n⟩).trans
      ⟨large_inputs d (m+1) n,large_private d (m+1) n⟩)

/-- The enlarged small families use the same complete two-member rotation
on both sides and on the original private-tree attachments. -/
theorem smallDouble_synchronous (d m n : Nat) :
    BoundaryIso.Synchronous (leftSmallDouble d m n) (rightSmallDouble d m n) :=
  (association_synchronous _ _ _ _ _ _).trans
    (((BoundaryIso.synchronous_refl _ _).tensor ⟨small_inputs d m n,small_private d m n⟩).trans
      ⟨small_inputs d m (n+1),small_private d m (n+1)⟩)

end Hypernets.Copying.Parametricity.FamilyLiteral
