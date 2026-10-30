import Hypernets.Copying.ParametricityFamilyCoordinates
import Hypernets.Copying.BoundaryParallel

/-! The generic family decomposition is identified with the original Figure20
families, preserving all actual edges, boxes, and boundary coordinates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyLiteral
open Graph Opening FamilyComponents

/-- The generic one-output presentation differs only in arithmetic index
proofs from the literal left family. -/
noncomputable def leftOccurrence (d m n : Nat) :
    Occurrence (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n) (leftFamily d m n) :=
  ((Occurrence.ofIso (DeepIso.refl (Net.Tensor.net (copies (k := 1) (largeLeft d) m)
    (copies (k := 1) (smallLeft (d+1)) n)))).reboundarySource _ _).reboundaryTarget _ _

/-- The zero-output counterpart retains the original right family exactly. -/
noncomputable def rightOccurrence (d m n : Nat) :
    Occurrence (family (k := 0) (largeRight d) (smallRight (d+1)) m n) (rightFamily d m n) :=
  ((Occurrence.ofIso (DeepIso.refl (Net.Tensor.net (copies (k := 0) (largeRight d) m)
    (copies (k := 0) (smallRight (d+1)) n)))).reboundarySource _ _).reboundaryTarget _ _

noncomputable def leftIso (d m n : Nat) :
    BoundaryIso (family (k := 1) (largeLeft d) (smallLeft (d+1)) m n) (leftFamily d m n) :=
  (leftOccurrence d m n).boundaryIso_of_edge_surjective
    (by intro i; trivial) (by intro i; trivial) (by intro e; exact ⟨e,rfl⟩)

noncomputable def rightIso (d m n : Nat) :
    BoundaryIso (family (k := 0) (largeRight d) (smallRight (d+1)) m n) (rightFamily d m n) :=
  (rightOccurrence d m n).boundaryIso_of_edge_surjective
    (by intro i; trivial) (by intro i; exact Fin.elim0 (Fin.cast (by simp) i)) (by intro e; exact ⟨e,rfl⟩)

theorem left_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftIso d m n).ports.toFun (.input i) = .input i := rfl

theorem right_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (rightIso d m n).ports.toFun (.input i) = .input i := rfl

theorem left_output (d m n : Nat) (i : Fin (List.replicate (1*(m+n)) Wire.term).length) :
    (leftIso d m n).ports.toFun (.output i) = .output ⟨i.val,by simpa using i.isLt⟩ := rfl

theorem left_inv_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftIso d m n).ports.invFun (.input i) = .input i := by
  rw [← left_input d m n i,Bijection.left_inv]

theorem right_inv_input (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (rightIso d m n).ports.invFun (.input i) = .input i := by
  rw [← right_input d m n i,Bijection.left_inv]

theorem left_inv_output (d m n : Nat) (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftIso d m n).ports.invFun (.output i) = .output ⟨i.val,by simpa using i.isLt⟩ := by
  have eq := left_output d m n ⟨i.val,by simpa using i.isLt⟩
  rw [← eq,Bijection.left_inv]

/-- The first large abstraction and the literal remaining left family. -/
noncomputable def leftLarge (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (largeLeft d) (leftFamily d m n)) (leftFamily d (m+1) n) :=
  ((BoundaryIso.refl _).tensor (leftIso d m n).symm).trans
    ((isolateLargeIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).trans (leftIso d (m+1) n))

/-- The first small abstraction and the literal remaining left family;
the boundary permutation rotates its private output with its input. -/
noncomputable def leftSmall (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (smallLeft (d+1)) (leftFamily d m n)) (leftFamily d m (n+1)) :=
  ((BoundaryIso.refl _).tensor (leftIso d m n).symm).trans
    ((isolateSmallIso (k := 1) (largeLeft d) (smallLeft (d+1)) m n).trans (leftIso d m (n+1)))

/-- Literal large-right isolation with exactly the same input ordering. -/
noncomputable def rightLarge (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (largeRight d) (rightFamily d m n)) (rightFamily d (m+1) n) :=
  ((BoundaryIso.refl _).tensor (rightIso d m n).symm).trans
    ((isolateLargeIso (k := 0) (largeRight d) (smallRight (d+1)) m n).trans (rightIso d (m+1) n))

/-- Literal small-right isolation with the same selected-input rotation. -/
noncomputable def rightSmall (d m n : Nat) :
    BoundaryIso (Net.Tensor.net (smallRight (d+1)) (rightFamily d m n)) (rightFamily d m (n+1)) :=
  ((BoundaryIso.refl _).tensor (rightIso d m n).symm).trans
    ((isolateSmallIso (k := 0) (largeRight d) (smallRight (d+1)) m n).trans (rightIso d m (n+1)))

end Hypernets.Copying.Parametricity.FamilyLiteral
