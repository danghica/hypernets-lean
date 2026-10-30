import Hypernets.Copying.ParametricityCopySource
import Hypernets.Copying.ParametricityCopyExecution

/-! Actual one-step copying through the complete original upstream graft at
the selected family member. Only arithmetic equality of interface lengths is
cast; every selected and untouched family input keeps its ordered position. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyExecution
open Graph Combined
variable {d a n k h : Nat} {O K : List Wire}
    (T : ContractionTree .term (a+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (R : Hypernet d (List.replicate n .term) O)

abbrev graftSource : Hypernet d (List.replicate (a+(n+1)) .term) (environmentInterface k h ++ O) :=
  (ContractionTree.Graft.net (s := .term) (T.atDepth d) (CopySource.whole H R) 0).reboundary
    (by congr 1;omega) rfl

noncomputable def sourceIso : DeepIso (graftSource T H R) (source T H R) := by
  have iso := CopyRule.reboundaryIso (CopySource.iso (T.atDepth d) H R)
    (by congr 1;omega : List.replicate ((a+1)+n) Wire.term = List.replicate (a+(n+1)) Wire.term) rfl
  unfold graftSource source CopyRule.before CopyRule.tree
  simpa only [CopySource.target,ShareSort.wire,CopyingMerge.reboundary_comp,ContractionTree.atDepth] using iso

/-- The entire original graft takes one actual original copying transition,
not a conditional step inferred from a future contextual-equivalence theorem. -/
theorem graft_rewrite (copyable : Copyable H) :
    Rewrite (graftSource T H R) (.input ⟨0,by simp <;> omega⟩)
      (target T H R) (.input ⟨0,by simp <;> omega⟩) :=
  (rewrite T H R copyable).rename (sourceIso T H R).symm (DeepIso.refl _)

private theorem serial_reboundary_input {d I I' J K}
    (G : Hypernet d I J) (C : Hypernet d J K) (hi : I=I') :
    Serial.net (G.reboundary hi rfl) C = (Serial.net G C).reboundary hi rfl := by
  cases hi;simp

abbrev continuedSource (C : Hypernet d (environmentInterface k h ++ O) K) :
    Hypernet d (List.replicate (a+(n+1)) .term) K :=
  (ContractionTree.Graft.net (s := .term) (T.atDepth d) (Serial.net (CopySource.whole H R) C) 0).reboundary
    (by congr 1;omega) rfl

noncomputable def continuedSourceIso (C : Hypernet d (environmentInterface k h ++ O) K) :
    DeepIso (continuedSource T H R C) (Serial.net (source T H R) C) := by
  have move := CopyRule.reboundaryIso
    (ContractionTree.Graft.SerialRight.iso (s := .term) (T.atDepth d) (CopySource.whole H R) C 0)
    (by congr 1;omega : List.replicate ((a+1)+n) Wire.term = List.replicate (a+(n+1)) Wire.term) rfl
  rw [← serial_reboundary_input] at move
  exact move.trans (Serial.congr (sourceIso T H R) (DeepIso.refl C))

/-- Private sharing and store remain inside the original family graft and
inside its computed successor; no closed-world or single-use condition occurs. -/
theorem continued_graft_rewrite (C : Hypernet d (environmentInterface k h ++ O) K)
    (copyable : Copyable H) :
    Rewrite (continuedSource T H R C) (.input ⟨0,by simp <;> omega⟩)
      (CopyContext.net (CopyRule.residual T d) (Serial.net (family H R) C))
      (.input ⟨0,by simp <;> omega⟩) :=
  (continued T H R C copyable).rename (continuedSourceIso T H R C).symm (DeepIso.refl _)

end Hypernets.Copying.Parametricity.CopyExecution
