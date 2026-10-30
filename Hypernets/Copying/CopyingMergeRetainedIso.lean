import Hypernets.Copying.CopyingMerge
import Hypernets.Copying.CopyingRetainedContext

/-! The one-active-input resource context is precisely the general merge,
with only its original arithmetic equality of interface lengths exposed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge
open Graph

theorem reboundary_comp {d I O I' O' I'' O''}
    (G : Hypernet d I O) (hi : I = I') (ho : O = O')
    (hi' : I' = I'') (ho' : O' = O'') :
    (G.reboundary hi ho).reboundary hi' ho' =
      G.reboundary (hi.trans hi') (ho.trans ho') := by
  cases hi; cases ho; cases hi'; cases ho'; simp

private theorem serial_reboundary {d I I' J K}
    (A : Hypernet d I J) (B : Hypernet d J K) (hi : I = I') :
    Serial.net (A.reboundary hi rfl) B = (Serial.net A B).reboundary hi rfl := by
  cases hi
  simp

/-- The generic merge with one active input preserves the exact original
copying reduct, including the arithmetic transport of its input interface. -/
noncomputable def retainedIso {d b k h : Nat}
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h)) :
    DeepIso (CopyingRetainedContext.after H B)
      ((net H B).reboundary (by rw [Nat.add_comm]) rfl) := by
  have eq : (pair H B).reboundary (by rw [Nat.add_comm]) rfl =
      CopyingRetainedContext.copies H B := by
    unfold pair CopyingRetainedContext.copies
    rw [reboundary_comp]
    rfl
  unfold net CopyingRetainedContext.after
  rw [← serial_reboundary,eq]
  exact DeepIso.refl _

/-- Independent recursive graph representations can be changed inside the
original two resource branches. -/
noncomputable def congr {d a b k h : Nat}
    {A A' : Hypernet d (List.replicate a .term) (environmentInterface k h)}
    {B B' : Hypernet d (List.replicate b .term) (environmentInterface k h)}
    (f : DeepIso A A') (g : DeepIso B B') : DeepIso (net A B) (net A' B') :=
  Serial.congr (CopyRule.reboundaryIso (ParallelPair.congr (boundary a b k h) f g) _ _)
    (DeepIso.refl _)

/-- Transporting the first branch's arithmetic arity commutes with its
unchanged merge context. -/
theorem reboundary_left {d a a' b k h : Nat}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))
    (eq : a = a') :
    net (A.reboundary (congrArg (fun n => List.replicate n Wire.term) eq) rfl) B =
      (net A B).reboundary (congrArg (fun n => List.replicate (n+b) Wire.term) eq) rfl := by
  subst a'; simp only [Net.reboundary_refl]

/-- The literal active/retained copying decomposition can be used as the
first branch of a further original resource merge. -/
noncomputable def retainedLeftIso {d b c k h : Nat}
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))
    (C : Hypernet d (List.replicate c .term) (environmentInterface k h)) :
    DeepIso (net (CopyingRetainedContext.after H B) C)
      ((net (net (a := 1) H B) C).reboundary (by congr 1; omega) rfl) := by
  have f := congr (retainedIso H B) (DeepIso.refl C)
  have eq := reboundary_left (net H B) C (show 1+b = b+1 by omega)
  rw [eq] at f
  exact f

/-- Exact graph representation changes pass through the original active
copy and all original canonical output distributors. -/
noncomputable def retainedCongr {d b k h : Nat}
    (H : Hypernet d [.term] (environmentInterface k h))
    {B C : Hypernet d (List.replicate b .term) (environmentInterface k h)}
    (f : DeepIso B C) :
    DeepIso (CopyingRetainedContext.after H B) (CopyingRetainedContext.after H C) :=
  Serial.congr (CopyRule.reboundaryIso
    (ParallelPair.congr (CopyRule.pairBoundary b k h) (DeepIso.refl H) f) _ _)
    (DeepIso.refl _)

end Hypernets.Copying.CopyingMerge
