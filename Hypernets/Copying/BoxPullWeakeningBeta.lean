import Hypernets.Copying.BoxPullWeakeningSplice
import Hypernets.Copying.BoxPullWeakeningSerial
import Hypernets.Copying.BoxPullWeakeningTensor
import Hypernets.Copying.BoxPullWeakeningRewrite

/-! Actual beta rewriting on BPullW's outside-weakening side. The graph
isomorphisms expose an instance of the original beta rule; stability of the
argument is retained as its original operational premise. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

def adjoin_congr {d I A B} {G H : Hypernet d I (A ++ B)}
    (f : DeepIso G H) (s : ShareSort) : DeepIso (adjoin G s) (adjoin H s) :=
  CopyRule.reboundaryIso (ParallelPair.congr (insertionBoundary I A B s) f (DeepIso.refl _)) _ _

/-- Equal ordered output interfaces can be transported outside an unchanged
serial prefix; no edge or shared internal wire is altered. -/
def serial_output {d I J K L} (G : Hypernet d I J) (H : Hypernet d J K)
    (ho : K = L) :
    DeepIso (Serial.net G (H.reboundary rfl ho)) ((Serial.net G H).reboundary rfl ho) := by
  cases ho
  simpa only [Net.reboundary_refl] using DeepIso.refl (Serial.net G H)

def boxedApplication {d F O} (X : Hypernet (d+1) [.thunk 1] F)
    (V : Hypernet (d+1) [.term] O) : Hypernet (d+1) [.term] (F ++ O) :=
  Serial.net (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (Serial.net (primitiveNet (d+1) (.operation .lam)) X) V)

/-- The unmodified app/lam prefix and argument can be separated from the
outside weakening with exactly the original boundary ordering. -/
def outside_source_iso {d A B O} (X : Hypernet (d+1) [.thunk 1] (A ++ B))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) :
    DeepIso (boxedApplication (adjoin X s) V)
      ((adjoin ((boxedApplication X V).reboundary rfl (List.append_assoc A B O)) s).reboundary
        rfl (by simp only [List.append_assoc,List.cons_append])) := by
  let lam := primitiveNet (d+1) (.operation .lam)
  let app := primitiveNet (d+1) (.operation .app)
  let C := Serial.net lam X
  let M := Net.Tensor.net C V
  let castOut : (A ++ s.wire :: (B ++ O)) = (A ++ s.wire :: B) ++ O := by
    simp only [List.append_assoc,List.cons_append]
  have first := Serial.congr (DeepIso.refl app)
    (ParallelPair.congr (Net.Tensor.boundary _ _ _ _) (SerialPull.iso lam X s) (DeepIso.refl V))
  have second := Serial.congr (DeepIso.refl app) (TensorPull.iso C V s)
  have third := serial_output app (adjoin (M.reboundary rfl (List.append_assoc A B O)) s) castOut
  have fourth := CopyRule.reboundaryIso (SerialPull.iso app (M.reboundary rfl (List.append_assoc A B O)) s) rfl castOut
  have fifth := CopyRule.reboundaryIso (adjoin_congr (serial_output app M (List.append_assoc A B O)) s) rfl castOut
  exact first.trans (second.trans (third.trans (fourth.trans fifth)))

/-- Open the original box and leave its external weakening where it was.
The target is the concrete splice with the same independent weakening; this
is an original machine rewrite, not an assumed semantic equivalence. -/
theorem outside_beta {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) (stable : Stable V) :
    Rewrite
      (boxedApplication (adjoin (A := List.replicate k .term) (B := List.replicate h .atom)
        (Translation.lambdaBox B) s) V) (.input 0)
      (Splice.right (A := List.replicate k .term) (B := List.replicate h .atom)
        (Application.openBody B) V s) (.input 0) := by
  let split : (environmentInterface k h ++ O) =
      List.replicate k Wire.term ++ (List.replicate h Wire.atom ++ O) := List.append_assoc _ _ _
  let order : List.replicate k Wire.term ++ s.wire :: (List.replicate h Wire.atom ++ O) =
      (List.replicate k Wire.term ++ s.wire :: List.replicate h Wire.atom) ++ O := by
    simp only [List.append_assoc,List.cons_append]
  have step := rewrite_reboundary rfl split (Rewrite.local (.beta B V stable))
  have step := adjoin_rewrite (I := [.term]) (A := List.replicate k .term)
    (B := List.replicate h .atom ++ O) s (0 : Fin 1) (0 : Fin 1) step
  have step := rewrite_reboundary rfl order step
  exact step.rename (outside_source_iso (Translation.lambdaBox B) V s).symm (DeepIso.refl _)

end Hypernets.Copying.BoxPullWeakening
