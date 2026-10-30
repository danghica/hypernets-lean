import Hypernets.Copying.ParametricityCopyResidual
import Hypernets.Copying.ParametricityDoubleFamily
import Hypernets.Copying.ParametricityBoundaryWitness
import Hypernets.Copying.BoundaryReboundary

/-! Genuine original Figure20 residual specimens after copying either
kind of abstraction, for arbitrary finite large and small families. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyFamilies
open Graph

private theorem outputCast_input {d I O J K U} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) (ho : O=U) (i : Fin I.length) :
    ((BoundaryIso.interfaceEquality G rfl ho).symm.trans f).inputs.toFun i = f.inputs.toFun i := by
  have back : (BoundaryIso.interfaceEquality G rfl ho).ports.invFun (.input i) = .input i := by
    have forward := BoundaryIso.interfaceEquality_port G rfl ho (.input i)
    change (BoundaryIso.interfaceEquality G rfl ho).ports.toFun (.input i) = .input i at forward
    rw [← forward,Bijection.left_inv]
  apply Port.input.inj (Internal := H.Internal) (outputs := K.length)
  dsimp only [BoundaryIso.inputs]
  rw [← BoundaryIso.map_input]
  change f.ports.toFun ((BoundaryIso.interfaceEquality G rfl ho).ports.invFun (.input i)) = _
  rw [back,f.map_input]

/-- Copying a large abstraction increases the large family by exactly one.
The old private tree is extended by the entire canonical two-input term row. -/
noncomputable def large (d m n : Nat) (C : ContractionTree .term ((m+n)+1)) :
    FillingWitness template
      (CopyGrowth.grownLeft (largeLeft d) (leftFamily d m n) C)
      (CopyGrowth.grownRight (largeRight d) (rightFamily d m n)) := by
  let raw := Net.Tensor.net (Net.Tensor.net (largeLeft d) (largeLeft d)) (leftFamily d m n)
  let ho : [Wire.term,Wire.term] ++ List.replicate (m+n) Wire.term = List.replicate (2+(m+n)) Wire.term := by
    exact List.replicate_append_replicate (n := 2)
  let f := (BoundaryIso.interfaceEquality raw rfl ho).symm.trans (FamilyLiteral.leftLargeDouble d m n)
  let g := FamilyLiteral.rightLargeDouble d m n
  have same : ∀ i, f.inputs.toFun i = g.inputs.toFun i := by
    intro i
    rw [outputCast_input]
    exact (FamilyLiteral.largeDouble_synchronous d m n).1 i
  have w := BoundaryWitness.filling_reboundary_tree (m := m+2) (n := n)
    (by omega : 2+(m+n) = (m+2)+n)
    (ho.trans (by congr 1;omega))
    f g (CopyGrowth.tree C) same
  exact w.reboundary (by simp only [List.replicate_succ];rfl) rfl

/-- Copying a small abstraction increases the small family by exactly one.
The two selected members move together past the large block; their private
outputs use the same proved permutation as both external input interfaces. -/
noncomputable def small (d m n : Nat) (C : ContractionTree .term ((m+n)+1)) :
    FillingWitness template
      (CopyGrowth.grownLeft (smallLeft (d+1)) (leftFamily d m n) C)
      (CopyGrowth.grownRight (smallRight (d+1)) (rightFamily d m n)) := by
  let raw := Net.Tensor.net (Net.Tensor.net (smallLeft (d+1)) (smallLeft (d+1))) (leftFamily d m n)
  let ho : [Wire.term,Wire.term] ++ List.replicate (m+n) Wire.term = List.replicate (2+(m+n)) Wire.term := by
    exact List.replicate_append_replicate (n := 2)
  let f := (BoundaryIso.interfaceEquality raw rfl ho).symm.trans (FamilyLiteral.leftSmallDouble d m n)
  let g := FamilyLiteral.rightSmallDouble d m n
  have same : ∀ i, f.inputs.toFun i = g.inputs.toFun i := by
    intro i
    rw [outputCast_input]
    exact (FamilyLiteral.smallDouble_synchronous d m n).1 i
  have w := BoundaryWitness.filling_reboundary_tree (m := m) (n := n+2)
    (by omega : 2+(m+n) = m+(n+2))
    (ho.trans (by congr 1;omega))
    f g (CopyGrowth.tree C) same
  exact w.reboundary (by simp only [List.replicate_succ];rfl) rfl

/-- Full original copy/copy diagram for a selected large abstraction and
arbitrarily many remaining large and small members. The only parameters are
actual finite trees and family sizes; the residual is a constructed specimen. -/
theorem large_copy {a} (d m n : Nat) (T : ContractionTree .term (a+1))
    (C : ContractionTree .term ((m+n)+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate (a+((m+n)+1)) .term) [],
      Combined.Rewrite
        (CopyExecution.continuedSource (k := 1) (h := 0) T (largeLeft d) (leftFamily d m n) (CopyGrowth.tail C))
        (.input ⟨0,by simp <;> omega⟩) A (.input ⟨0,by simp <;> omega⟩) ∧
      Combined.Rewrite
        (CopyExecution.graftSource (k := 0) (h := 0) T (largeRight d) (rightFamily d m n))
        (.input ⟨0,by simp <;> omega⟩) B (.input ⟨0,by simp <;> omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  refine ⟨CopyContext.net (CopyRule.residual T (d+2))
    (Serial.net (CopyExecution.family (k := 1) (h := 0) (largeLeft d) (leftFamily d m n)) (CopyGrowth.tail C)),
    CopyExecution.target (k := 0) (h := 0) T (largeRight d) (rightFamily d m n),?_⟩
  exact CopyGrowth.diagram (largeLeft d) (leftFamily d m n) C T
    (.lambda (callReadBody d)) (.lambda (callOneBody d)) (large d m n C)

/-- The corresponding complete original diagram for any selected small
abstraction. The private-cell pointer is duplicated through the original
canonical term row; the right closed abstraction has no private pointer. -/
theorem small_copy {a} (d m n : Nat) (T : ContractionTree .term (a+1))
    (C : ContractionTree .term ((m+n)+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate (a+((m+n)+1)) .term) [],
      Combined.Rewrite
        (CopyExecution.continuedSource (k := 1) (h := 0) T (smallLeft (d+1)) (leftFamily d m n) (CopyGrowth.tail C))
        (.input ⟨0,by simp <;> omega⟩) A (.input ⟨0,by simp <;> omega⟩) ∧
      Combined.Rewrite
        (CopyExecution.graftSource (k := 0) (h := 0) T (smallRight (d+1)) (rightFamily d m n))
        (.input ⟨0,by simp <;> omega⟩) B (.input ⟨0,by simp <;> omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  refine ⟨CopyContext.net (CopyRule.residual T (d+2))
    (Serial.net (CopyExecution.family (k := 1) (h := 0) (smallLeft (d+1)) (leftFamily d m n)) (CopyGrowth.tail C)),
    CopyExecution.target (k := 0) (h := 0) T (smallRight (d+1)) (rightFamily d m n),?_⟩
  exact CopyGrowth.diagram (smallLeft (d+1)) (leftFamily d m n) C T
    (.lambda (readBody (d+1))) (.lambda (oneBody (d+1))) (small d m n C)

end Hypernets.Copying.Parametricity.CopyFamilies
