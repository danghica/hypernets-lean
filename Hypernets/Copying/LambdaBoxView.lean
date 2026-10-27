import Hypernets.Copying.DecorationAssembly

/-! The canonical box classification at the unchanged translated lambda interface. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

/-- Equality transport round trips without changing any vertex or edge. -/
theorem cast_roundtrip {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet d I O) :
    Translation.castInterfaces hi.symm ho.symm (Translation.castInterfaces hi ho G) = G := by
  cases hi; cases ho; rfl

def undoBodyCast {d I O K} (eq : O = K) (B : Hypernet d I O) (C : Hypernet d I K)
    (f : BoundaryIso (Translation.castInterfaces rfl eq B) C) :
    BoundaryIso B (Translation.castInterfaces rfl eq.symm C) := by cases eq; exact f

theorem undoBodyCast_action {d I O K} (eq : O = K) (B : Hypernet d I O) (C : Hypernet d I K)
    (f : BoundaryIso (Translation.castInterfaces rfl eq B) C) (p : TypedPermutation K)
    (action : ∀ i, f.outputs.toFun i = p.bijection.toFun i) :
    ∀ i, (undoBodyCast eq B C f).outputs.toFun i = (TypedPermutation.cast eq.symm p).bijection.toFun i := by
  cases eq; exact action

inductive LambdaView {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.thunk 1] (environmentInterface k h) → Type 1 where
  | retained {H} (iso : DeepIso (Translation.lambdaBox B) H) : LambdaView B H
  | deep {C H} (body : FillingWitness template B C) (iso : DeepIso (Translation.lambdaBox C) H) : LambdaView B H
  | shallow {C H} (p : TypedPermutation (environmentInterface k h)) (body : BoundaryIso B C)
      (action : Opening.Action body p)
      (iso : DeepIso (InterfacePermutation.net (Translation.lambdaBox C) p.symm) H) : LambdaView B H

/-- Retained, deep, and shallow are exhaustive, including representation changes. -/
noncomputable def AtomicPair.lambdaView {d k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {H : Hypernet (d+1) [.thunk 1] (environmentInterface k h)}
    (pair : AtomicPair (Translation.lambdaBox B) H) : LambdaView B H := by
  let eq : environmentInterface (k+1) h = environmentInterface (1+k) h := congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1)
  let A := Translation.castInterfaces rfl eq B
  have view : BoxView A H := pair.boxView
  cases view with
  | retained f => exact .retained f
  | @deep C H body f =>
    let C' := Translation.castInterfaces rfl eq.symm C
    have w : FillingWitness template B C' := by
      simpa only [A,cast_roundtrip] using body.interfaces rfl eq.symm
    have iso : DeepIso (Translation.lambdaBox C') H := by
      simpa only [Translation.lambdaBox,C',cast_roundtrip] using f
    exact .deep w iso
  | @shallow C H p body action f =>
    let C' := Translation.castInterfaces rfl eq.symm C
    let bc : BoundaryIso B C' := undoBodyCast eq B C body
    have act : Opening.Action bc p.outer := by
      have actInner : ∀ i, body.outputs.toFun i = (inner 1 p.outer).bijection.toFun i :=
        fun i => (action i).trans (p.unique i)
      have transported := undoBodyCast_action eq B C body (inner 1 p.outer) actInner
      simpa only [bc,inner,TypedPermutation.cast_trans,Opening.Action,Opening.bodyPermutation] using transported
    have iso : DeepIso (InterfacePermutation.net (Translation.lambdaBox C') p.outer.symm) H := by
      simpa only [Translation.lambdaBox,C',cast_roundtrip] using f
    exact .shallow p.outer bc act iso
end Hypernets.Copying.BoxPermutation
