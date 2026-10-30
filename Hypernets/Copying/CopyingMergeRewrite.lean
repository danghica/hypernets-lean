import Hypernets.Copying.CopyingMerge
import Hypernets.Copying.ParallelContextPlug

/-! Actual original rewrites inside the first branch of a resource merge.
The other branch and both complete canonical distributor families remain. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge
open Graph Combined
variable {d a b k h : Nat}
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))

def leftContext := ParallelPair.net (boundary a b k h)
  (primitiveNet d (.hole ⟨0,List.replicate a .term,environmentInterface k h⟩)) B

def leftHole : (leftContext (a := a) B).Edge := by
  cases d <;> exact ⟨false,(0 : Fin 1)⟩

noncomputable def leftIso
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h)) :
    DeepIso ((leftContext B).plug (leftHole B)
      (A.reboundary (by cases d <;> rfl) (by cases d <;> rfl)))
      (ParallelPair.net (boundary a b k h) A B) := by
  cases d
  all_goals
    simp only [Net.reboundary_refl]
    exact (DeepIso.ofIso (ParallelPair.plug_left (boundary a b k h)
      (primitiveNet _ (.hole ⟨0,List.replicate a .term,environmentInterface k h⟩)) B (0 : Fin 1) A)).trans
      (ParallelPair.congr _
        (DeepIso.ofIso (Net.corolla_plug_iso
          (primitiveLabel _ (.hole ⟨0,List.replicate a .term,environmentInterface k h⟩)) A)) (DeepIso.refl B))

/-- The selected original first-branch ports retain exactly their indices. -/
theorem pair_left_rewrite
    {A D : Hypernet d (List.replicate a .term) (environmentInterface k h)}
    (i j : Fin (List.replicate a Wire.term).length)
    (step : Rewrite A (.input i) D (.input j)) :
    Rewrite (pair A B) (.input ⟨i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩)
      (pair D B) (.input ⟨j.val,by have := j.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  cases d
  all_goals
    have lifted := Rewrite.plug (leftContext (a := a) B) (leftHole (a := a) B) step
    have lifted := lifted.rename
      (by simpa only [Net.reboundary_refl] using leftIso B A)
      (by simpa only [Net.reboundary_refl] using leftIso B D)
    have changed := rewrite_reboundary (J := List.replicate (a+b) Wire.term)
      (K := environmentInterface (k*2) (h*2)) (by simp [List.replicate_append_replicate])
      (by simp [environmentInterface,Nat.mul_two]) lifted
    simpa [pair,ParallelPair.net,Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,
      leftContext,leftHole,Net.Parallel.net,Net.Parallel.incidence,Net.Tensor.family,
      primitiveNet,Net.corolla,boundary,Net.Parallel.embed,Net.Tensor.ports,
      Net.Tensor.join,List.getElem_map,List.getElem_finRange,Port.map,Port.cast]
      using changed

/-- The actual merge closure keeps all resource edges and the untouched second
branch, and takes exactly one original compute rewrite when the branch does. -/
theorem left_rewrite
    {A D : Hypernet d (List.replicate a .term) (environmentInterface k h)}
    (i j : Fin (List.replicate a Wire.term).length)
    (step : Rewrite A (.input i) D (.input j)) :
    Rewrite (net A B) (.input ⟨i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩)
      (net D B) (.input ⟨j.val,by have := j.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  have inside := pair_left_rewrite B i j step
  cases d
  all_goals
    have outer := Rewrite.expand (Serial.pattern _ _ _ _)
      (Serial.filling (pair A B) (Translation.environmentDistributor _ k h 2))
      (Serial.filling (pair D B) (Translation.environmentDistributor _ k h 2)) false
      (by intro side ne; cases side; exact False.elim (ne rfl); rfl) inside
    simpa [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Serial.pattern,
      List.getElem_map,List.getElem_finRange,Port.map,net,Serial.net] using outer

end Hypernets.Copying.CopyingMerge
