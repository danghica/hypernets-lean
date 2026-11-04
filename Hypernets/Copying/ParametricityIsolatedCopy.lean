import Hypernets.Copying.ParametricityCopyFamilies
import Hypernets.Copying.ParametricityIsolatedFamily

/-! The checked original family-copy diagrams expressed as literal grafts
into complete isolated Figure20 families, including their exact private tree.
This is a change of graph presentation only; no copying rule is altered. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.IsolatedCopy
open Graph Combined ContractionTree

private theorem serial_middle {d I J K O} (A : Hypernet d I J) (B : Hypernet d K O) (eq : J=K) :
    Serial.net A (B.reboundary eq.symm rfl) = Serial.net (A.reboundary rfl eq) B := by
  cases eq
  simp only [Net.reboundary_refl]

private theorem uncast_source {d I J O} (A : Hypernet d I O) (eq : I=J)
    {B : Hypernet d J O} (i : Fin I.length)
    (step : Rewrite (A.reboundary eq rfl) (.input (Fin.cast (congrArg List.length eq) i))
      B (.input (Fin.cast (congrArg List.length eq) i))) :
    Rewrite A (.input i) (B.reboundary eq.symm rfl) (.input i) := by
  cases eq
  rw [Net.reboundary_refl A] at step
  rw [Net.reboundary_refl B]
  exact step

/-- Equal list presentations at the private wires and serial reassociation
identify the copy diagram's continuation with the full isolated original
family, tree and cell. Every edge and all external ports are preserved. -/
noncomputable def closedIso {d n} (H : Hypernet d [.term] [.term])
    (R : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (C : ContractionTree .term (n+1)) :
    DeepIso (Serial.net (CopySource.whole H R) (CopyGrowth.tail C))
      (Serial.net (Serial.net ((Net.Tensor.net H R).reboundary
        (by simp [List.replicate_succ]) (by simp [List.replicate_succ,ShareSort.wire])) (C.atDepth d)) (privateCell d)) := by
  let eq : [Wire.term] ++ List.replicate n Wire.term = List.replicate (n+1) Wire.term := by
    simp [List.replicate_succ]
  have first := serial_middle (CopySource.whole H R) (Serial.net (C.atDepth d) (privateCell d)) eq
  change DeepIso (Serial.net (CopySource.whole H R)
    ((Serial.net (C.atDepth d) (privateCell d)).reboundary eq.symm rfl)) _
  rw [first]
  have same : (CopySource.whole H R).reboundary rfl eq =
      (Net.Tensor.net H R).reboundary (by simp [List.replicate_succ]) (by simp [List.replicate_succ]) := by
    unfold CopySource.whole
    rw [reboundary_comp]
  rw [same]
  exact (Serial.Association.iso _ _ _).symm

/-- An arbitrary upstream term tree copies the first isolated large member
in one transition on each side, with a constructed original parametricity
residual. Both sources are literal grafts of complete original families. -/
theorem large {a} (d m n : Nat) (P : ContractionTree .term (a+1))
    (C : ContractionTree .term ((m+n)+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate ((a+1)+(m+n)) .term) [],
      Rewrite (Graft.net (P.atDepth (d+2)) (IsolatedFamily.largeClosed d C) 0)
        (.input ⟨0,by simp <;> omega⟩) A (.input ⟨0,by simp <;> omega⟩) ∧
      Rewrite (Graft.net (P.atDepth (d+2)) (IsolatedFamily.largeRightFamily d m n) 0)
        (.input ⟨0,by simp <;> omega⟩) B (.input ⟨0,by simp <;> omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  obtain ⟨A,B,left,right,⟨w⟩⟩ := CopyFamilies.large_copy d m n P C
  let eq : List.replicate (a+((m+n)+1)) Wire.term = List.replicate ((a+1)+(m+n)) Wire.term := by congr 1; omega
  have li := Graft.congr (DeepIso.refl (P.atDepth (d+2)))
    (closedIso (largeLeft d) (leftFamily d m n) C) (0 : Fin ((m+n)+1))
  have sourceLeft : Rewrite
      (Graft.net (P.atDepth (d+2)) (Serial.net (CopySource.whole (largeLeft d) (leftFamily d m n)) (CopyGrowth.tail C)) 0)
      (.input ⟨0,by simp <;> omega⟩) (A.reboundary eq rfl) (.input ⟨0,by simp <;> omega⟩) := by
    exact uncast_source _ eq.symm ⟨0,by simp <;> omega⟩ left
  have sourceRight : Rewrite
      (Graft.net (P.atDepth (d+2)) (IsolatedFamily.largeRightFamily d m n) 0)
      (.input ⟨0,by simp <;> omega⟩) (B.reboundary eq rfl) (.input ⟨0,by simp <;> omega⟩) := by
    exact uncast_source _ eq.symm ⟨0,by simp <;> omega⟩ right
  exact ⟨_,_,sourceLeft.rename li (DeepIso.refl _),sourceRight,⟨w.reboundary eq rfl⟩⟩

/-- The same complete literal graft diagram copies the first isolated small
member, preserving all untouched family members and the exact old tree. -/
theorem small {a} (d m n : Nat) (P : ContractionTree .term (a+1))
    (C : ContractionTree .term ((m+n)+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate ((a+1)+(m+n)) .term) [],
      Rewrite (Graft.net (P.atDepth (d+2)) (IsolatedFamily.smallClosed d C) 0)
        (.input ⟨0,by simp <;> omega⟩) A (.input ⟨0,by simp <;> omega⟩) ∧
      Rewrite (Graft.net (P.atDepth (d+2)) (IsolatedFamily.smallRightFamily d m n) 0)
        (.input ⟨0,by simp <;> omega⟩) B (.input ⟨0,by simp <;> omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  obtain ⟨A,B,left,right,⟨w⟩⟩ := CopyFamilies.small_copy d m n P C
  let eq : List.replicate (a+((m+n)+1)) Wire.term = List.replicate ((a+1)+(m+n)) Wire.term := by congr 1; omega
  have li := Graft.congr (DeepIso.refl (P.atDepth (d+2)))
    (closedIso (smallLeft (d+1)) (leftFamily d m n) C) (0 : Fin ((m+n)+1))
  have sourceLeft : Rewrite
      (Graft.net (P.atDepth (d+2)) (Serial.net (CopySource.whole (smallLeft (d+1)) (leftFamily d m n)) (CopyGrowth.tail C)) 0)
      (.input ⟨0,by simp <;> omega⟩) (A.reboundary eq rfl) (.input ⟨0,by simp <;> omega⟩) := by
    exact uncast_source _ eq.symm ⟨0,by simp <;> omega⟩ left
  have sourceRight : Rewrite
      (Graft.net (P.atDepth (d+2)) (IsolatedFamily.smallRightFamily d m n) 0)
      (.input ⟨0,by simp <;> omega⟩) (B.reboundary eq rfl) (.input ⟨0,by simp <;> omega⟩) := by
    exact uncast_source _ eq.symm ⟨0,by simp <;> omega⟩ right
  exact ⟨_,_,sourceLeft.rename li (DeepIso.refl _),sourceRight,⟨w.reboundary eq rfl⟩⟩

end Hypernets.Copying.Parametricity.IsolatedCopy
