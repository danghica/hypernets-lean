import Hypernets.Copying.RetainedDecoration
import Hypernets.Copying.BetaDecoration

/-! Original lambda-body views and exact shallow-hole properties of copied
recursive residuals. Nested operational holes remain allowed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Opening.Occurrence
theorem allLabels {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : Occurrence A G) (P : Primitive → Prop) (labels : AllLabels P G) : AllLabels P A :=
  fun e => (labelAll_equiv P d (f.label e)).mpr (labels (f.edges e))
end Opening.Occurrence

namespace RetainedAtomic
variable {T : PreTemplate}

inductive LambdaView {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.thunk 1] (environmentInterface k h) → Type 1 where
  | retained {H} (iso : DeepIso (Translation.lambdaBox B) H) : LambdaView B H
  | deep {C H} (body : FillingWitness T B C) (binding : BindingFree body.context)
      (iso : DeepIso (Translation.lambdaBox C) H) : LambdaView B H

noncomputable def lambdaView {d k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {H : Hypernet (d+1) [.thunk 1] (environmentInterface k h)}
    (pair : RetainedAtomic T (Translation.lambdaBox B) H) : LambdaView (T := T) B H := by
  let eq : environmentInterface (k+1) h = environmentInterface (1+k) h := congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1)
  let A := Translation.castInterfaces rfl eq B
  have view : BoxView (T := T) A H := pair.boxView
  cases view with
  | retained f => exact .retained f
  | @deep C H body binding f =>
    let C' := Translation.castInterfaces rfl eq.symm C
    have round : Translation.castInterfaces rfl eq.symm A = B := BoxPermutation.cast_roundtrip rfl eq B
    let w : {w : FillingWitness T B C' // BindingFree w.context} :=
      Eq.mp (congrArg (fun X => {w : FillingWitness T X C' // BindingFree w.context}) round)
        ⟨body.interfaces rfl eq.symm,body.interfaces_binding _ _ binding⟩
    have iso : DeepIso (Translation.lambdaBox C') H := by
      simpa only [Translation.lambdaBox,C',BoxPermutation.cast_roundtrip] using f
    exact .deep w.1 w.2 iso
end RetainedAtomic

namespace FillingWitness
variable {T : PreTemplate}

theorem serial_no_shallow_holes {d I J K} {G G' : Hypernet d I J} {H H' : Hypernet d J K}
    (g : FillingWitness T G G') (h : FillingWitness T H H')
    (gc : ∀ e, ¬ HoleLabel d (g.context.edgeLabel e)) (hc : ∀ e, ¬ HoleLabel d (h.context.edgeLabel e)) :
    ∀ e, ¬ HoleLabel d ((g.serial h).context.edgeLabel e) := by
  rw [serial_context]
  intro ⟨b,e⟩
  cases d <;> cases b
  all_goals first | exact gc e | exact hc e

theorem holeFree_no_shallow {d I O} {G : Hypernet d I O} (closed : HoleFree G) :
    ∀ e, ¬ HoleLabel d (G.edgeLabel e) := by
  rintro e ⟨h,label⟩
  have impossible := closed e
  rw [label] at impossible
  cases d <;> exact impossible h rfl

theorem copies_no_shallow_holes {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (active retained : FillingWitness T G H) (tree : ContractionTree .term (n+1))
    (ac : ∀ e, ¬ HoleLabel d (active.context.edgeLabel e))
    (rc : ∀ e, ¬ HoleLabel d (retained.context.edgeLabel e)) :
    ∀ e, ¬ HoleLabel d ((copies active retained tree).context.edgeLabel e) := by
  unfold copies
  rw [reboundary_context]
  intro ⟨b,e⟩
  cases b with
  | false => exact ac e
  | true =>
    have closed : HoleFree (CopyRule.residual tree d) :=
      CopyRule.residual_allLabels _ tree d (by intro h eq; cases eq) (by intro h eq; cases eq)
    have focus : FocusFree (CopyRule.residual tree d) :=
      CopyRule.residual_allLabels _ tree d (by intro h eq; cases eq) (by intro h eq; cases eq)
    exact serial_no_shallow_holes (refl _ focus) retained (holeFree_no_shallow closed) rc e

theorem copyingAfter_no_shallow_holes {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (active retained : FillingWitness T G H) (tree : ContractionTree .term (n+1))
    (ac : ∀ e, ¬ HoleLabel d (active.context.edgeLabel e))
    (rc : ∀ e, ¬ HoleLabel d (retained.context.edgeLabel e)) :
    ∀ e, ¬ HoleLabel d ((copyingAfter active retained tree).context.edgeLabel e) :=
  serial_no_shallow_holes _ _ (copies_no_shallow_holes active retained tree ac rc)
    (holeFree_no_shallow (Translation.language_holeFree (Translation.environmentDistributor_language _ _ _ _)))

theorem deepCopy_no_shallow_holes {d n k h}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (w : FillingWitness T B C) (tree : ContractionTree .term (n+1)) :
    ∀ e, ¬ HoleLabel (d+1) ((w.deepCopy tree).context.edgeLabel e) :=
  copyingAfter_no_shallow_holes _ _ tree w.lambdaPayload_no_shallow_holes w.lambdaPayload_no_shallow_holes

end FillingWitness
end Hypernets.Copying
