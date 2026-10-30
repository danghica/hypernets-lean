import Hypernets.Copying.ParametricityCopyGrowth
import Hypernets.Copying.ParametricityCopyGraftExecution
import Hypernets.Copying.ParametricityTemplate

/-! The selected-copy residual keeps a single enlarged Figure20 specimen
inside the actual common upstream residual context. Both compute steps are
original Figure17 rules; the private cell is never replaced by an abstract store. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyGrowth
open Graph

private theorem serial_reboundary_input {d I I' J K}
    (G : Hypernet d I J) (C : Hypernet d J K) (hi : I=I') :
    (Serial.net G C).reboundary hi rfl = Serial.net (G.reboundary hi rfl) C := by
  cases hi;simp

variable {d n : Nat} (H : Hypernet d [.term] [.term])
    (R : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (C : ContractionTree .term (n+1))

abbrev grownLeft : Hypernet d (List.replicate ((n+1)+1) .term) [] :=
  (after H R C).reboundary (by simp only [List.replicate_succ];rfl) rfl

/-- Express the exact private-resource normalization at the common enlarged
family interface expected by the residual-input context. -/
noncomputable def normalizedIso : DeepIso
    (Serial.net (CopyExecution.family (k := 1) (h := 0) H R) (tail C)) (grownLeft H R C) := by
  have f := CopyRule.reboundaryIso (iso H R C)
    (by simp only [List.replicate_succ];rfl :
      [Wire.term,Wire.term] ++ List.replicate n Wire.term = List.replicate ((n+1)+1) Wire.term) rfl
  rw [before,serial_reboundary_input] at f
  exact f

abbrev grownRight (H : Hypernet d [.term] []) (R : Hypernet d (List.replicate n .term) []) :
    Hypernet d (List.replicate ((n+1)+1) .term) [] :=
  (Net.Tensor.net (Net.Tensor.net H H) R).reboundary (by simp only [List.replicate_succ];rfl) rfl

noncomputable def normalizedClosedIso (H : Hypernet d [.term] [])
    (R : Hypernet d (List.replicate n .term) []) :
    DeepIso (CopyExecution.family (k := 0) (h := 0) H R) (grownRight H R) :=
  CopyRule.reboundaryIso (closedIso H R) (by simp only [List.replicate_succ];rfl) rfl

/-- An independently proved enlarged-family certificate lifts through exactly
one common residual-input context, retaining the active and all other inputs. -/
noncomputable def witness {a} (T : ContractionTree .term (a+1))
    {H' : Hypernet d [.term] []} {R' : Hypernet d (List.replicate n .term) []}
    (grown : FillingWitness template (grownLeft H R C) (grownRight H' R')) :
    FillingWitness template
      (CopyContext.net (CopyRule.residual T d)
        (Serial.net (CopyExecution.family (k := 1) (h := 0) H R) (tail C)))
      (CopyExecution.target (k := 0) (h := 0) T H' R') :=
  CopyContext.witness (CopyRule.residual T d)
    (ContractionAlgebra.tree_focusFree (CopyRule.residualTree T) d)
    (grown.congr (normalizedIso H R C).symm (normalizedClosedIso H' R').symm)

/-- Actual original copying on both complete grafted families, together with
its original enlarged-family specimen. The premises on copied bodies are the
original copyability judgments; no machine or template law is assumed. -/
theorem diagram {a} (T : ContractionTree .term (a+1))
    {H' : Hypernet d [.term] []} {R' : Hypernet d (List.replicate n .term) []}
    (leftCopyable : Copyable (k := 1) (h := 0) H) (rightCopyable : Copyable (k := 0) (h := 0) H')
    (grown : FillingWitness template (grownLeft H R C) (grownRight H' R')) :
    Combined.Rewrite
      (CopyExecution.continuedSource (k := 1) (h := 0) T H R (tail C)) (.input ⟨0,by simp <;> omega⟩)
      (CopyContext.net (CopyRule.residual T d)
        (Serial.net (CopyExecution.family (k := 1) (h := 0) H R) (tail C))) (.input ⟨0,by simp <;> omega⟩) ∧
    Combined.Rewrite (CopyExecution.graftSource (k := 0) (h := 0) T H' R') (.input ⟨0,by simp <;> omega⟩)
      (CopyExecution.target (k := 0) (h := 0) T H' R') (.input ⟨0,by simp <;> omega⟩) ∧
    Nonempty (FillingWitness template
      (CopyContext.net (CopyRule.residual T d)
        (Serial.net (CopyExecution.family (k := 1) (h := 0) H R) (tail C)))
      (CopyExecution.target (k := 0) (h := 0) T H' R')) := by
  constructor
  · exact CopyExecution.continued_graft_rewrite (k := 1) (h := 0) T H R (tail C) leftCopyable
  constructor
  · exact CopyExecution.graft_rewrite (k := 0) (h := 0) T H' R' rightCopyable
  · exact ⟨witness H R C T grown⟩

end Hypernets.Copying.Parametricity.CopyGrowth
