import Hypernets.Copying.CopyingAfterInputPermutation
import Hypernets.Copying.CopyingDoubleSearch
import Hypernets.Copying.CopyingDoubleWitness

/-! Normalize an arbitrary second selected input to position one, perform the
literal two-copy diagram, and restore the complete original input ordering. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDoubleAt
open Graph Combined CopyingInputPermutation

variable {d n k h : Nat} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))
    (j : Fin (List.replicate (n+2) Wire.term).length)

def ordering : TypedPermutation (List.replicate (n+2) .term) :=
  swap .term (n+2) ⟨1,by simp⟩ j

theorem ordering_one : (ordering j).bijection.invFun ⟨1,by simp⟩ = j := by
  simp [ordering,swap,exchange]

theorem ordering_zero (positive : 0 < j.val) :
    (ordering j).bijection.toFun ⟨0,by simp⟩ = ⟨0,by simp⟩ := by
  simp [ordering,swap,exchange]
  intro eq
  have bad := congrArg Fin.val eq
  simp only [Fin.val_zero] at bad
  omega

noncomputable def normalized : ContractionTree .term (n+2) := reordered T (ordering j)

/-- The actual first-copy successor when the entered original input is j. -/
noncomputable def leftAfter : Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  net (net (CopyRule.after (reordered (normalized T j) (CopyingDouble.exchangeInputs n)) H)
    (CopyingDouble.exchangeInputs n)) (ordering j).symm

/-- The actual second-copy successor on the original template's right side. -/
noncomputable def rightAfter : Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  net (CopyingDouble.afterSecond (normalized T j) H) (ordering j).symm

/-- Source equality here is an isomorphism of full ordered graphs, obtained
from two actual original copies and proved successor coherence. -/
noncomputable def rightSourceIso (copyable : Copyable H) (positive : 0 < j.val) :
    DeepIso (CopyRule.after T H) (net (CopyRule.after (normalized T j) H) (ordering j).symm) :=
  (roundtrip (CopyRule.after T H) (ordering j)).trans
    (congr (afterIso T H copyable (ordering j) (ordering_zero j positive)) (ordering j).symm)

/-- The first original copy at input one, in the normalized presentation. -/
theorem normalized_left_rewrite (copyable : Copyable H) :
    Rewrite (CopyRule.before (normalized T j) H) (.input ⟨1,by simp⟩)
      (net (CopyRule.after (reordered (normalized T j) (CopyingDouble.exchangeInputs n)) H)
        (CopyingDouble.exchangeInputs n)) (.input ⟨1,by simp⟩) := by
  have act := CopyingInputPermutation.rewrite (CopyingDouble.exchangeInputs n)
    ⟨0,by simp⟩ ⟨0,by simp⟩
    (.local (.copy (reordered (normalized T j) (CopyingDouble.exchangeInputs n)) H copyable))
  have selected : (CopyingDouble.exchangeInputs n).bijection.toFun ⟨0,by simp⟩ = ⟨1,by simp⟩ := by
    simp [CopyingDouble.exchangeInputs,swap,exchange]
  rw [selected] at act
  exact act.rename (beforeIso (normalized T j) H (CopyingDouble.exchangeInputs n)).symm (DeepIso.refl _)

/-- No branch or input is omitted: this is an actual original rewrite at j. -/
theorem left_rewrite (copyable : Copyable H) :
    Rewrite (CopyRule.before T H) (.input j) (leftAfter T H j) (.input j) := by
  have act := CopyingInputPermutation.rewrite (ordering j).symm
    ⟨1,by simp⟩ ⟨1,by simp⟩ (normalized_left_rewrite T H j copyable)
  change Rewrite _ (.input ((ordering j).bijection.invFun ⟨1,by simp⟩)) _
    (.input ((ordering j).bijection.invFun ⟨1,by simp⟩)) at act
  rw [ordering_one] at act
  exact act.rename (beforeIso T H (ordering j)).symm (DeepIso.refl _)

/-- The other side performs its next actual original copy at the same j. -/
theorem right_rewrite (copyable : Copyable H) (positive : 0 < j.val) :
    Rewrite (CopyRule.after T H) (.input j) (rightAfter T H j) (.input j) := by
  have act := CopyingInputPermutation.rewrite (ordering j).symm
    ⟨1,by simp⟩ ⟨1,by simp⟩ (CopyingDouble.second_rewrite H (normalized T j) copyable)
  change Rewrite _ (.input ((ordering j).bijection.invFun ⟨1,by simp⟩)) _
    (.input ((ordering j).bijection.invFun ⟨1,by simp⟩)) at act
  rw [ordering_one] at act
  exact act.rename (rightSourceIso T H j copyable positive).symm (DeepIso.refl _)

/-- The right side's retained tree still requests copying in exactly one
search transition at every nonzero original input. -/
theorem right_request (copyable : Copyable H) (positive : 0 < j.val) :
    Search.Step (CopyRule.after T H) (.search,.input j) (.rewrite,.input j) := by
  have first := CopyingDouble.afterWith_request H _ ⟨0,by simp⟩
    (CopyingTemplate.requests_copy (CopyRule.residualTree (normalized T j)) H ⟨0,by simp⟩)
  have mapped := (Search.ofBoundaryIso (iso (CopyRule.after (normalized T j) H) (ordering j).symm)).step first
  change Search.Step _ (.search,.input ((ordering j).bijection.invFun ⟨1,by simp⟩))
    (.rewrite,.input ((ordering j).bijection.invFun ⟨1,by simp⟩)) at mapped
  rw [ordering_one] at mapped
  exact (Search.ofBoundaryIso (BoundaryIso.ofDeepIso (rightSourceIso T H j copyable positive).symm)).step mapped

/-- Both sides of the non-distinguished-input diagram take exactly two
original machine transitions, irrespective of payload or environment size. -/
theorem entry (copyable : Copyable H) (positive : 0 < j.val) :
    (Combined.machine d (List.replicate (n+2) .term) (environmentInterface k h)).Steps 2
      ⟨CopyRule.before T H,(.search,.input j)⟩ ⟨leftAfter T H j,(.search,.input j)⟩ ∧
    (Combined.machine d (List.replicate (n+2) .term) (environmentInterface k h)).Steps 2
      ⟨CopyRule.after T H,(.search,.input j)⟩ ⟨rightAfter T H j,(.search,.input j)⟩ :=
  ⟨.cons (.search _ (CopyingTemplate.requests_copy T H j))
    (.cons (.rewrite (left_rewrite T H j copyable)) (.zero _)),
   .cons (.search _ (right_request T H j copyable positive))
    (.cons (.rewrite (right_rewrite T H j copyable positive)) (.zero _))⟩

end Hypernets.Copying.CopyingDoubleAt
