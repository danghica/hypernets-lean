import Hypernets.Copying.CopyingDouble
import Hypernets.Copying.ParallelContextPlug
import Hypernets.Copying.CombinedPadding

/-! The second original copying step occurs in the retained branch of the
literal first reduct. The outer active copy and canonical distributors remain. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble
open Graph Combined

variable {d n k h : Nat} (H : Hypernet d [.term] (environmentInterface k h))

def retainedContext := ParallelPair.net (CopyRule.pairBoundary (n+1) k h) H
  (primitiveNet d (.hole ⟨0,List.replicate (n+1) .term,environmentInterface k h⟩))

def retainedHole : (retainedContext (n := n) H).Edge := by
  cases d <;> exact ⟨true,(0 : Fin 1)⟩

noncomputable def retainedIso
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) :
    DeepIso ((retainedContext H).plug (retainedHole H)
      (K.reboundary (by cases d <;> rfl) (by cases d <;> rfl)))
      (ParallelPair.net (CopyRule.pairBoundary (n+1) k h) H K) := by
  cases d
  all_goals
    simp only [Net.reboundary_refl]
    exact (DeepIso.ofIso (ParallelPair.plug_right (CopyRule.pairBoundary (n+1) k h) H
      (primitiveNet _ (.hole ⟨0,List.replicate (n+1) .term,environmentInterface k h⟩)) (0 : Fin 1) K)).trans
      (ParallelPair.congr _ (DeepIso.refl H)
        (DeepIso.ofIso (Net.corolla_plug_iso
          (primitiveLabel _ (.hole ⟨0,List.replicate (n+1) .term,environmentInterface k h⟩)) K)))

/-- A real retained-branch rewrite keeps the active copy and preserves the
original external positions: retained input i is external input i+1. -/
theorem copiesWith_rewrite
    {A B : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (i j : Fin (List.replicate (n+1) Wire.term).length)
    (step : Rewrite A (.input i) B (.input j)) :
    Rewrite (copiesWith H A) (.input ⟨i.val+1,by have bound := i.isLt; simp only [List.length_replicate] at *; omega⟩)
      (copiesWith H B) (.input ⟨j.val+1,by have bound := j.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  cases d
  all_goals
    have lifted := Rewrite.plug (retainedContext (n := n) H) (retainedHole (n := n) H) step
    have lifted := lifted.rename
      (by simpa only [Net.reboundary_refl] using retainedIso H A)
      (by simpa only [Net.reboundary_refl] using retainedIso H B)
    have changed := rewrite_reboundary (J := List.replicate (n+2) Wire.term)
      (K := environmentInterface (k*2) (h*2)) (by simp [List.replicate_succ])
      (by simp [environmentInterface,Nat.mul_two]) lifted
    simpa [copiesWith,ParallelPair.net,Nat.add_comm,Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,
      retainedContext,retainedHole,Net.Parallel.net,Net.Parallel.incidence,Net.Tensor.family,
      primitiveNet,Net.corolla,CopyRule.pairBoundary,Net.Parallel.embed,Net.Tensor.ports,
      Net.Tensor.join,List.getElem_map,List.getElem_finRange,Port.map,Port.cast]
      using changed

/-- The surrounding original resource distributor is also retained by the
compute step, using the machine's actual simultaneous-expansion closure. -/
theorem afterWith_rewrite
    {A B : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (i j : Fin (List.replicate (n+1) Wire.term).length)
    (step : Rewrite A (.input i) B (.input j)) :
    Rewrite (afterWith H A) (.input ⟨i.val+1,by have bound := i.isLt; simp only [List.length_replicate] at *; omega⟩)
      (afterWith H B) (.input ⟨j.val+1,by have bound := j.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  have inside := copiesWith_rewrite H i j step
  cases d
  all_goals
    have outer := Rewrite.expand (Serial.pattern _ _ _ _)
      (Serial.filling (copiesWith H A) (Translation.environmentDistributor _ k h 2))
      (Serial.filling (copiesWith H B) (Translation.environmentDistributor _ k h 2)) false
      (by intro b ne; cases b; exact False.elim (ne rfl); rfl) inside
    simpa [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Serial.pattern,
      List.getElem_map,List.getElem_finRange,Port.map,afterWith,Serial.net] using outer

/-- Copying original input one of the displayed reduct is exactly a second
original Figure 17 rewrite, with no algebraic contraction step inserted. -/
theorem second_rewrite (T : ContractionTree .term (n+2)) (copyable : Copyable H) :
    Rewrite (CopyRule.after T H) (.input ⟨1,by simp⟩)
      (afterSecond T H) (.input ⟨1,by simp⟩) :=
  afterWith_rewrite H ⟨0,by simp⟩ ⟨0,by simp⟩
    (.local (.copy (CopyRule.residualTree T) H copyable))

end Hypernets.Copying.CopyingDouble
