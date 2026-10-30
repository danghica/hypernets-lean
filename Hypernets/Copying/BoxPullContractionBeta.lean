import Hypernets.Copying.BoxPullContractionSplice
import Hypernets.Copying.BoxPullContractionSerial
import Hypernets.Copying.BoxPullContractionTensor
import Hypernets.Copying.BoxPullContractionRewrite
import Hypernets.Copying.BoxPullWeakeningBeta

/-! Actual beta rewriting with an external contraction. Isomorphisms expose
exactly the original app/lam/box redex and preserve its stable argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined

abbrev boxedApplication := @BoxPullWeakening.boxedApplication

/-- The unchanged app/lam prefix and argument can be factored through the
literal contraction frame, with all remaining output positions preserved. -/
def outside_source_iso {d A B O} (s : ShareSort)
    (X : Hypernet (d+1) [.thunk 1] (A ++ s.wire :: s.wire :: B))
    (V : Hypernet (d+1) [.term] O) :
    DeepIso (boxedApplication (merge s X) V)
      ((merge (A := A) (B := B ++ O) s ((boxedApplication X V).reboundary rfl
        (by simp only [List.append_assoc,List.cons_append]))).reboundary
        rfl (by simp only [List.append_assoc,List.cons_append])) := by
  let lam := primitiveNet (d+1) (.operation .lam)
  let app := primitiveNet (d+1) (.operation .app)
  let C := Serial.net lam X
  let M := Net.Tensor.net C V
  let split : (A ++ s.wire :: s.wire :: B) ++ O =
      A ++ s.wire :: s.wire :: (B ++ O) := by simp only [List.append_assoc,List.cons_append]
  let castOut : (A ++ s.wire :: (B ++ O)) = (A ++ s.wire :: B) ++ O := by
    simp only [List.append_assoc,List.cons_append]
  have first := Serial.congr (DeepIso.refl app)
    (ParallelPair.congr (Net.Tensor.boundary _ _ _ _) (SerialPull.iso s lam X) (DeepIso.refl V))
  have second := Serial.congr (DeepIso.refl app) (TensorPull.iso s C V)
  have third := BoxPullWeakening.serial_output app (merge s (M.reboundary rfl split)) castOut
  have fourth := CopyRule.reboundaryIso (SerialPull.iso s app (M.reboundary rfl split)) rfl castOut
  have fifth := CopyRule.reboundaryIso (merge_congr s
    (BoxPullWeakening.serial_output app M split)) rfl castOut
  exact first.trans (second.trans (third.trans (fourth.trans fifth)))

/-- A literal output contraction carries any actual app/lam-prefix rewrite
through unchanged. This theorem transports an existing machine step; it is
not an additional compute rule. -/
theorem outside_rewrite {d A B O} (s : ShareSort)
    (X : Hypernet (d+1) [.thunk 1] (A ++ s.wire :: s.wire :: B))
    (V : Hypernet (d+1) [.term] O)
    {H : Hypernet (d+1) [.term] ((A ++ s.wire :: s.wire :: B) ++ O)}
    (step : Rewrite (boxedApplication X V) (.input 0) H (.input 0)) :
    Rewrite (boxedApplication (merge s X) V) (.input 0)
      ((merge (A := A) (B := B ++ O) s (H.reboundary rfl
        (by simp only [List.append_assoc,List.cons_append]))).reboundary
        rfl (by simp only [List.append_assoc,List.cons_append])) (.input 0) := by
  have step := rewrite_reboundary rfl
    (show (A ++ s.wire :: s.wire :: B) ++ O = A ++ s.wire :: s.wire :: (B ++ O) from by
      simp only [List.append_assoc,List.cons_append]) step
  have step := merge_rewrite (I := [.term]) (A := A) (B := B ++ O) s (0 : Fin 1) (0 : Fin 1) step
  have step := rewrite_reboundary rfl
    (show A ++ s.wire :: (B ++ O) = (A ++ s.wire :: B) ++ O from by
      simp only [List.append_assoc,List.cons_append]) step
  exact step.rename (outside_source_iso s X V).symm (DeepIso.refl _)

/-- Moving an equality of ordered free interfaces through the app/lam frame
changes no edge, argument, or bound-output connection. -/
def boxedApplication_output {d F F' O} (X : Hypernet (d+1) [.thunk 1] F)
    (V : Hypernet (d+1) [.term] O) (ho : F = F') :
    DeepIso (boxedApplication (X.reboundary rfl ho) V)
      ((boxedApplication X V).reboundary rfl (congrArg (fun F => F ++ O) ho)) := by
  cases ho
  simpa only [Net.reboundary_refl] using DeepIso.refl (boxedApplication X V)

/-- The original beta rule, with its original stability premise, really
fires through an outside contraction. The body and argument are unchanged;
the equality only locates the displayed pair in the ordered free boundary. -/
theorem outside_beta {d k h A B O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (stable : Stable V)
    (ho : environmentInterface k h = A ++ s.wire :: s.wire :: B) :
    Rewrite (boxedApplication (merge s ((Translation.lambdaBox G).reboundary rfl ho)) V) (.input 0)
      ((merge (A := A) (B := B ++ O) s ((Application.after G V).reboundary rfl
        ((congrArg (fun F => F ++ O) ho).trans
          (by simp only [List.append_assoc,List.cons_append])))).reboundary
        rfl (by simp only [List.append_assoc,List.cons_append])) (.input 0) := by
  have step := rewrite_reboundary rfl (congrArg (fun F => F ++ O) ho)
    (Rewrite.local (.beta G V stable))
  have step := step.rename (boxedApplication_output (Translation.lambdaBox G) V ho).symm (DeepIso.refl _)
  have step := outside_rewrite s ((Translation.lambdaBox G).reboundary rfl ho) V step
  rw [reboundary_comp] at step
  exact step

/-- Both sharing sorts and every environment size instantiate the displayed
pair without any additional premise about ordered interfaces. -/
theorem outside_beta_environment {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) (stable : Stable V) :
    Rewrite (boxedApplication (merge (A := List.replicate k .term) (B := List.replicate h .atom) s
      ((Translation.lambdaBox G).reboundary rfl (by simpa using block_interface s k h 2))) V) (.input 0)
      ((merge (A := List.replicate k .term) (B := List.replicate h .atom ++ O) s
        ((Application.after G V).reboundary rfl (by
          simpa only [List.append_assoc,List.cons_append] using
            congrArg (fun F => F ++ O) (show environmentInterface (variables s k 2) (atoms s h 2) =
              List.replicate k .term ++ s.wire :: s.wire :: List.replicate h .atom from by
                simpa using block_interface s k h 2)))).reboundary
        rfl (by simp only [List.append_assoc,List.cons_append])) (.input 0) :=
  outside_beta s G V stable (by simpa using block_interface s k h 2)

end Hypernets.Copying.BoxPullContraction
