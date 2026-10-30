import Hypernets.Copying.UnrestrictedDecoration
import Hypernets.Copying.RetainedLocalViews

/-! Full original lambda-body views without binding-free side conditions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace UnrestrictedAtomic
variable {T : PreTemplate}

inductive LambdaView {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.thunk 1] (environmentInterface k h) → Type 1 where
  | retained {H} (iso : DeepIso (Translation.lambdaBox B) H) : LambdaView B H
  | deep {C H} (body : FillingWitness T B C)
      (iso : DeepIso (Translation.lambdaBox C) H) : LambdaView B H

noncomputable def lambdaView {d k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {H : Hypernet (d+1) [.thunk 1] (environmentInterface k h)}
    (pair : UnrestrictedAtomic T (Translation.lambdaBox B) H) : LambdaView (T := T) B H := by
  let eq : environmentInterface (k+1) h = environmentInterface (1+k) h := congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1)
  let A := Translation.castInterfaces rfl eq B
  have view : BoxView (T := T) A H := pair.boxView
  cases view with
  | retained f => exact .retained f
  | @deep C H body f =>
    let C' := Translation.castInterfaces rfl eq.symm C
    have round : Translation.castInterfaces rfl eq.symm A = B := BoxPermutation.cast_roundtrip rfl eq B
    let w : FillingWitness T B C' :=
      Eq.mp (congrArg (fun X => FillingWitness T X C') round)
        (body.interfaces rfl eq.symm)
    have iso : DeepIso (Translation.lambdaBox C') H := by
      simpa only [Translation.lambdaBox,C',BoxPermutation.cast_roundtrip] using f
    exact .deep w iso
end UnrestrictedAtomic
end Hypernets.Copying
