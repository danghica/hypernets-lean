import Hypernets.Copying.BoxPullContractionAtomic
import Hypernets.Copying.LambdaBoxView

/-! Exhaustive atomic BPullC views, including the actual shallower outside box
and its external contraction. Representation changes do not erase this case. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

inductive AtomicNormal : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Type 1 where
  | iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : AtomicNormal G H
  | shallow {d n k h I O} {G H : Hypernet (d+1) I O} (s : ShareSort)
      (hi : [.thunk n] = I) (ho : environmentInterface (variables s k 1) (atoms s h 1) = O)
      (C : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) (free : FocusFree C)
      (leftIso : DeepIso G ((left s C).reboundary hi ho))
      (rightIso : DeepIso ((right s C).reboundary hi ho) H) : AtomicNormal G H
  | deep {d n k h I O} {G H : Hypernet (d+1) I O}
      (hi : [.thunk n] = I) (ho : environmentInterface k h = O)
      {B C : Hypernet d [.term] (environmentInterface (n+k) h)}
      (left : DeepIso G ((box (bound := n) (freeVariables := k) B).reboundary hi ho))
      (body : FillingWitness template B C)
      (right : DeepIso ((box (bound := n) (freeVariables := k) C).reboundary hi ho) H) : AtomicNormal G H

namespace AtomicNormal
noncomputable def congr {d I O} {G H A B : Hypernet d I O} (pair : AtomicNormal G H)
    (f : DeepIso A G) (g : DeepIso H B) : AtomicNormal A B := by
  cases pair with
  | iso h => exact .iso (f.trans (h.trans g))
  | shallow s hi ho C free l r => exact .shallow s hi ho C free (f.trans l) (r.trans g)
  | deep hi ho l body r => exact .deep hi ho (f.trans l) body (r.trans g)

def interfaces {d I O J K} {G H : Hypernet d I O} (pair : AtomicNormal G H)
    (hi : I = J) (ho : O = K) : AtomicNormal (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using pair
end AtomicNormal

noncomputable def UpToIso.normal {d I O} {G H : Hypernet d I O} (rel : UpToIso G H) :
    AtomicNormal G H := by
  apply Classical.choice
  cases rel with
  | witness l step r =>
    cases step with
    | pull s C free => exact ⟨.shallow s rfl rfl C free
        (by simpa only [Net.reboundary_refl] using l)
        (by simpa only [Net.reboundary_refl] using r)⟩

noncomputable def AtomicPair.normal {d I O} {G H : Hypernet d I O} (pair : AtomicPair G H) :
    AtomicNormal G H := by
  induction pair with
  | iso f => exact .iso f
  | shallow rel => exact rel.normal
  | boxed body =>
    exact .deep rfl rfl (by simpa only [Net.reboundary_refl] using DeepIso.refl _) body
      (by simpa only [Net.reboundary_refl] using DeepIso.refl _)
  | congr f pair g ih => exact ih.congr f g
  | interfaces hi ho pair ih => exact ih.interfaces hi ho

/-- A shallow lambda keeps its exact expanded body on the left and its original
uncontracted lambda box plus external contraction on the right. -/
inductive LambdaView {d : Nat} : {k h : Nat} →
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) →
    Hypernet (d+1) [.thunk 1] (environmentInterface k h) → Type 1 where
  | retained {k h B H} (iso : DeepIso (Translation.lambdaBox B) H) : @LambdaView d k h B H
  | deep {k h B C H} (body : FillingWitness template B C)
      (iso : DeepIso (Translation.lambdaBox C) H) : @LambdaView d k h B H
  | shallow {k h s}
      {B : Hypernet d [.term] (environmentInterface (variables s k 1+1) (atoms s h 1))}
      {H : Hypernet (d+1) [.thunk 1] (environmentInterface (variables s k 1) (atoms s h 1))}
      (C : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) (free : FocusFree C)
      (leftIso : DeepIso (Translation.lambdaBox B) (Translation.lambdaBox (betaBody s C)))
      (rightIso : DeepIso (contract s (Translation.lambdaBox C)) H) : LambdaView B H

/-- These three cases exhaust every original atomic certificate at a lambda
box; equality of recursive labels fixes all binding and free-interface counts. -/
noncomputable def AtomicPair.lambdaView {d k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {H : Hypernet (d+1) [.thunk 1] (environmentInterface k h)}
    (pair : AtomicPair (Translation.lambdaBox B) H) : LambdaView B H := by
  apply Classical.choice
  cases pair.normal with
  | iso f => exact ⟨.retained f⟩
  | @deep d n' k' h' I O G H hi ho A C l body r =>
    have related := l.edge_label (0 : Fin 1)
    change BoxRelated (alphabet d) (fun X Y => Nonempty (DeepIso X Y))
      ⟨1,k,h,Translation.castInterfaces rfl _ B⟩ ⟨n',k',h',A⟩ at related
    cases related with
    | bodies iso =>
      obtain ⟨f⟩ := iso
      let eq : environmentInterface (k+1) h = environmentInterface (1+k) h :=
        congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1)
      let C' := Translation.castInterfaces rfl eq.symm C
      have w : FillingWitness template B C' := by
        simpa only [BoxPermutation.cast_roundtrip] using
          (body.congr f.symm (DeepIso.refl _)).interfaces rfl eq.symm
      have target : DeepIso (Translation.lambdaBox C') H := by
        simpa only [Translation.lambdaBox,C',BoxPermutation.cast_roundtrip,Net.reboundary_refl] using r
      exact ⟨.deep w target⟩
  | @shallow d n' k' h' I O G H s hi ho C free l r =>
    have related := l.edge_label (0 : Fin 1)
    change BoxRelated (alphabet d) (fun X Y => Nonempty (DeepIso X Y))
      ⟨1,k,h,Translation.castInterfaces rfl _ B⟩
      ⟨n',variables s k' 1,atoms s h' 1,body s C⟩ at related
    cases related with
    | bodies iso =>
      let C' := C.reboundary rfl (congrArg (fun n => environmentInterface n (atoms s h' 2)) (Nat.add_comm 1 (variables s k' 2)))
      have round : C'.reboundary rfl (by rw [Nat.add_comm (variables s k' 2) 1]) = C := by
        simp only [C',reboundary_comp,Net.reboundary_refl]
      have source : DeepIso (Translation.lambdaBox B) (Translation.lambdaBox (betaBody s C')) := by
        rw [lambda_left,round]
        simpa only [Net.reboundary_refl] using l
      have target : DeepIso (contract s (Translation.lambdaBox C')) H := by
        rw [← lambda_right,round]
        simpa only [Net.reboundary_refl] using r
      exact ⟨.shallow C' free source target⟩

end Hypernets.Copying.BoxPullContraction
