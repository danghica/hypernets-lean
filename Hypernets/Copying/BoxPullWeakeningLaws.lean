import Hypernets.Copying.BoxPullWeakening
import Hypernets.Copying.FillingPadding

/-! BPullW's structural side conditions and actual allowance invariance.
The thunk input establishes operational input safety, but does not by itself
establish robustness under beta or copying. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph

/-- A box-pulling pair has precisely its original thunk input. -/
theorem template_noTermInputs : template.NoTermInputs := by
  intro d I O G H rel
  cases rel with
  | witness _ step _ =>
    cases step with
    | pull B s free =>
      intro i
      have eq : i = 0 := Fin.ext (by
        have := i.isLt
        change i.val < 1 at this
        change i.val = 0
        omega)
      subst i
      exact Wire.noConfusion

theorem template_outputClosed : template.OutputClosed := template_noTermInputs.outputClosed

/-- The actual term token cannot enter a BPullW hole. This proves safety
for every observation class and both orientations of every cost relation. -/
theorem template_inputSafe (Allowed : ∀ d, Hypernet d [.term] [] → Prop)
    (Q P : CostOrder) :
    (Specimens.system template Allowed template_outputClosed).InputSafe Q P :=
  Specimens.inputSafe_of_no_term_inputs template template_noTermInputs
    Allowed template_outputClosed Q P

/-- Increasing allowance preserves the exact typed parallel assembly. -/
theorem insert_raise {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    Copying.raise d (insert G s) = insert (Copying.raise d G) s := by
  unfold insert
  rw [Padding.parallel]
  congr 1
  funext b
  cases b
  · rfl
  · exact Padding.primitive d _

theorem extend_raise {d I k h} (G : Hypernet d I (environmentInterface k h))
    (s : ShareSort) :
    Copying.raise d (extend G s) = extend (Copying.raise d G) s := by
  unfold extend
  rw [CopyRule.raise_reboundary,insert_raise]

theorem body_raise {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) :
    Copying.raise d (body G s) = body (Copying.raise d G) s := by
  unfold body
  rw [CopyRule.raise_reboundary,extend_raise]

theorem left_raise {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) :
    Copying.raise (d+1) (left G s) = left (Copying.raise d G) s := by
  unfold left
  rw [Padding.box,body_raise]

theorem right_raise {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) :
    Copying.raise (d+1) (right G s) = right (Copying.raise d G) s := by
  unfold right
  rw [extend_raise,Padding.box]

/-- A padded literal pair is again a literal pair; the body and weakening
positions, and the complete recursive shape of the body, are preserved. -/
theorem Step.raise {d I O} {G H : Hypernet d I O} (step : Step G H) :
    Step (Copying.raise d G) (Copying.raise d H) := by
  cases step with
  | pull B s free =>
    rw [left_raise,right_raise]
    exact .pull _ s ((allLabels_raise_iff _ _ _).mpr free)

theorem UpToIso.raise {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f step g =>
    exact .witness (Padding.congr f) step.raise (Padding.congr g)

theorem template_paddingClosed : template.PaddingClosed := @UpToIso.raise

end Hypernets.Copying.BoxPullWeakening
