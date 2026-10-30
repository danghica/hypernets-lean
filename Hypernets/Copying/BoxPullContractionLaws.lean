import Hypernets.Copying.BoxPullContraction
import Hypernets.Copying.FillingPadding

/-! Structural safety and exact representation padding for Figure 21's
box-contraction pair. Its arbitrary body and both sharing sorts are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

theorem template_noTermInputs : template.NoTermInputs := by
  intro d I O G H pair
  cases pair with
  | witness _ step _ =>
    cases step with
    | pull s B free =>
      intro i
      have eq : i = 0 := Fin.ext (by
        have := i.isLt
        change i.val < 1 at this
        change i.val = 0
        omega)
      subst i
      exact Wire.noConfusion

theorem template_outputClosed : template.OutputClosed := template_noTermInputs.outputClosed

/-- A term token cannot enter the original thunk interface, for either
quantitative direction and every original context class. -/
theorem template_inputSafe (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (Q P : CostOrder) :
    (Specimens.system template Allowed template_outputClosed).InputSafe Q P :=
  Specimens.inputSafe_of_no_term_inputs template template_noTermInputs Allowed template_outputClosed Q P

/-- Padding preserves the complete output-merging frame and the body placed
in its original hole, including the contraction's two distinct junctions. -/
noncomputable def merge_raise {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) :
    DeepIso (Copying.raise d (merge s G)) (merge s (Copying.raise d G)) := by
  have iso : DeepIso (Copying.raise d (merge s G))
      ((Padding.graph (pattern d I A B s)).expand (Padding.expandFilling (pattern d I A B s) (filling s G))) := by
    simpa only [Padding.graph_eq_raise,merge] using
      DeepIso.ofIso (Padding.expand_graph (pattern d I A B s) (filling s G))
  apply iso.trans
  cases d
  all_goals
    apply Net.ExpansionIso.iso
    intro b
    cases b
    · simp only [Padding.expandFilling,Padding.graph_eq_raise]
      change DeepIso ((Copying.raise _ G).reboundary rfl rfl) (Copying.raise _ G)
      simpa only [Net.reboundary_refl] using DeepIso.refl (Copying.raise _ G)
    · exact DeepIso.refl _

noncomputable def contract_raise {d I k h} (s : ShareSort)
    (G : Hypernet d I (environmentInterface (variables s k 2) (atoms s h 2))) :
    DeepIso (Copying.raise d (contract s G)) (contract s (Copying.raise d G)) := by
  unfold contract
  rw [Padding.castInterfaces]
  apply Translation.castInterfaces_congr
  have iso := merge_raise s (Translation.castInterfaces rfl
    (by simpa using block_interface s k h 2) G)
  rw [Padding.castInterfaces] at iso
  exact iso

noncomputable def body_raise {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    DeepIso (Copying.raise d (body s G)) (body s (Copying.raise d G)) := by
  unfold body
  rw [Padding.castInterfaces]
  apply Translation.castInterfaces_congr
  have iso := contract_raise s (Translation.castInterfaces rfl (by rw [variables_bound]) G)
  rw [Padding.castInterfaces] at iso
  exact iso

noncomputable def left_raise {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    DeepIso (Copying.raise (d+1) (left s G)) (left s (Copying.raise d G)) := by
  unfold left
  rw [Padding.box]
  exact box_congr (body_raise s G)

noncomputable def right_raise {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    DeepIso (Copying.raise (d+1) (right s G)) (right s (Copying.raise d G)) := by
  unfold right
  simpa only [Padding.box] using contract_raise s (box (bound := n) (freeVariables := variables s k 2) G)

/-- The padded literal pair is the same BPullC pair up to its original
ordered recursive graph representation, with no added compute rule. -/
theorem Step.raise {d I O} {G H : Hypernet d I O} (step : Step G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases step with
  | pull s B free =>
    exact .witness (left_raise s B)
      (.pull s _ ((allLabels_raise_iff _ _ _).mpr free)) (right_raise s B).symm

theorem UpToIso.raise {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    UpToIso (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f step g =>
    cases step.raise with
    | witness l step r => exact .witness ((Padding.congr f).trans l) step (r.trans (Padding.congr g))

theorem template_paddingClosed : template.PaddingClosed := @UpToIso.raise

end Hypernets.Copying.BoxPullContraction
