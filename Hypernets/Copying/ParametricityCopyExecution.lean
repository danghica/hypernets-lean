import Hypernets.Copying.ParametricityCopyExtension
import Hypernets.Copying.ParametricityCopyNormalization
import Hypernets.Copying.ParametricityCopyAssembly
import Hypernets.Copying.ParametricityTensorCut

/-! One original lambda-copying step with an arbitrary retained family and
arbitrary serial continuation. Exact target normalization exposes the enlarged
family, retaining the full upstream residual tree in a common input context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined.Rewrite
open Graph Opening

/-- Lift an actual rewrite in the first tensor component without altering
any edge or ordered port of the second component. -/
theorem tensor_left {d I O J K} {A B : Hypernet d I O} (R : Hypernet d J K)
    (i j : Fin I.length) (step : Combined.Rewrite A (.input i) B (.input j)) :
    Combined.Rewrite (Net.Tensor.net A R) (.input (Net.Tensor.join I J ⟨false,i⟩))
      (Net.Tensor.net B R) (.input (Net.Tensor.join I J ⟨false,j⟩)) := by
  have act := (CompleteMatchCut.TensorLeft.selected A R).rewrite step
  have resume := CompleteMatchCut.TensorLeft.first_input A B R j
  change CompleteMatchCut.replacePort _ _ B (.input j) = _ at resume
  rw [resume] at act
  exact act.rename (DeepIso.refl _) (CompleteMatchCut.TensorLeft.iso A B R).symm

/-- Serial continuation preserves an actual rewrite and its two input
coordinates, including the resumed active family member. -/
theorem serial_left {d I J K} {A B : Hypernet d I J} (C : Hypernet d J K)
    (i j : Fin I.length) (step : Combined.Rewrite A (.input i) B (.input j)) :
    Combined.Rewrite (Serial.net A C) (.input i) (Serial.net B C) (.input j) := by
  cases d
  all_goals
    have lifted := Combined.Rewrite.expand (Serial.pattern _ I J K)
      (Serial.filling A C) (Serial.filling B C) false
      (by intro side ne; cases side; exact False.elim (ne rfl); rfl) step
    simpa [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Serial.pattern,
      List.getElem_map,List.getElem_finRange,Port.map,Serial.net] using lifted
end Hypernets.Copying.Combined.Rewrite

namespace Hypernets.Copying.Parametricity.CopyExecution
open Graph Combined
variable {d a n k h : Nat} {O K : List Wire}
    (T : ContractionTree .term (a+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (R : Hypernet d (List.replicate n .term) O)

abbrev source : Hypernet d (List.replicate (a+(n+1)) .term) (environmentInterface k h ++ O) :=
  (Net.Tensor.net (CopyRule.before T H) R).reboundary
    (by rw [List.replicate_append_replicate]; congr 1; omega) rfl
abbrev family : Hypernet d (List.replicate ((n+1)+1) .term) (environmentInterface k h ++ O) :=
  CopyExtension.whole (CopyingMerge.net (a := 1) (b := 1) H H) R
abbrev target := CopyContext.net (CopyRule.residual T d) (family H R)

/-- The whole original selected copying rule fires exactly once. Its target
contains the literal enlarged two-payload family and every original other
family member, with the original active input still zero. -/
theorem rewrite (copyable : Copyable H) :
    Rewrite (source T H R) (.input ⟨0,by simp <;> omega⟩)
      (target T H R) (.input ⟨0,by simp <;> omega⟩) := by
  have act := (CopyNormalization.rewrite H T copyable).tensor_left R ⟨0,by simp⟩ ⟨0,by simp⟩
  have moved := rewrite_reboundary
    (by rw [List.replicate_append_replicate]; congr 1; omega :
      List.replicate (a+1) Wire.term ++ List.replicate n Wire.term = List.replicate (a+(n+1)) Wire.term)
    rfl act
  exact moved.rename (DeepIso.refl _) (CopyExtension.iso (CopyRule.residual T d)
    (CopyingMerge.net (a := 1) (b := 1) H H) R).symm

/-- The same actual compute step retains an arbitrary private sharing/store
continuation and exposes it inside the common residual-input context. -/
theorem continued (C : Hypernet d (environmentInterface k h ++ O) K)
    (copyable : Copyable H) :
    Rewrite (Serial.net (source T H R) C) (.input ⟨0,by simp <;> omega⟩)
      (CopyContext.net (CopyRule.residual T d) (Serial.net (family H R) C))
      (.input ⟨0,by simp <;> omega⟩) := by
  exact ((rewrite T H R copyable).serial_left C ⟨0,by simp <;> omega⟩ ⟨0,by simp <;> omega⟩).rename
    (DeepIso.refl _) (CopyContext.serial (CopyRule.residual T d) (family H R) C).symm

end Hypernets.Copying.Parametricity.CopyExecution
