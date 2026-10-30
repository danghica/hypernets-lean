import Hypernets.Copying.CopyingDoubleFrame
import Hypernets.Copying.BoxPullWeakeningCopyRow
import Hypernets.Copying.BoxPullWeakeningReverseLambda
import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.BoxPullWeakeningCopyInjection

/-! Complete actual occurrences of all components of two literal copies. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble.Components
open Graph Opening
variable {d n k h}

/-- Both branches occur before the unchanged outer distributor. -/
def pair (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) (b : Bool) :
    Occurrence (Net.Tensor.family H K b) (copiesWith H K) where
  ports v := Port.cast (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])
    (Net.Parallel.embed (Net.Tensor.family H K) (CopyRule.pairBoundary (n+1) k h) b v)
  internals v := ⟨b,v⟩
  edges e := ⟨b,e⟩
  internal_map _ := rfl
  internal_injective := by intro a c eq; exact eq_of_heq (Sigma.mk.inj eq).2
  edge_injective := by intro a c eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source e := by
    change ((Net.Tensor.family H K b).source e).map _ = (((Net.Tensor.family H K b).source e).map _).map _
    rw [List.map_map]; rfl
  target e := by
    change ((Net.Tensor.family H K b).target e).map _ = (((Net.Tensor.family H K b).target e).map _).map _
    rw [List.map_map]; rfl

noncomputable def branch (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) (b : Bool) :
    Occurrence (Net.Tensor.family H K b) (afterWith H K) :=
  (pair H K b).comp (BoxPullWeakening.ReverseComponents.serialLeft _ _)

variable (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))

noncomputable def first : Occurrence H (afterSecond T H) := branch H _ false
noncomputable def retained : Occurrence (CopyRule.after (CopyRule.residualTree T) H) (afterSecond T H) := branch H _ true

/-- The second active payload has its original nested occurrence. -/
noncomputable def second : Occurrence H (afterSecond T H) :=
  ((BoxPullWeakening.RetainedCopy.copyComponent (CopyRule.residualTree T) H false).comp
    (BoxPullWeakening.ReverseComponents.serialLeft _ _)).comp (retained T H)

noncomputable def remaining : Occurrence
    (Serial.net (CopyRule.residual (CopyRule.residualTree T) d) H) (afterSecond T H) :=
  ((BoxPullWeakening.RetainedCopy.copyComponent (CopyRule.residualTree T) H true).comp
    (BoxPullWeakening.ReverseComponents.serialLeft _ _)).comp (retained T H)

noncomputable def third : Occurrence H (afterSecond T H) :=
  (Occurrence.serialRight _ _).comp (remaining T H)

noncomputable def tree : Occurrence ((CopyRule.residualTree (CopyRule.residualTree T)).atDepth d)
    (afterSecond T H) :=
  (BoxPullWeakening.ReverseComponents.serialLeft _ _).comp (remaining T H)

noncomputable def outerDistributor : Occurrence (Translation.environmentDistributor d k h 2) (afterSecond T H) :=
  Occurrence.serialRight _ _

noncomputable def innerDistributor : Occurrence (Translation.environmentDistributor d k h 2) (afterSecond T H) :=
  (Occurrence.serialRight _ _).comp (retained T H)


theorem pair_input_left (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) :
    (pair H K false).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  exact congrArg Port.input (Fin.ext rfl)

theorem pair_input_right (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h))
    (i : Fin (List.replicate (n+1) Wire.term).length) :
    (pair H K true).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
  apply congrArg Port.input
  apply Fin.ext
  change 1+i.val=i.val+1
  omega

theorem pair_output (H : Hypernet d [.term] (environmentInterface k h))
    (K : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h))
    (b : Bool) (i : Fin (environmentInterface k h).length) :
    (pair H K b).ports (.output (by cases b <;> exact i)) =
      .output (CopyRule.copyOutput k h b i) := by
  cases b <;> exact congrArg Port.output (Fin.ext rfl)

theorem first_input : (first T H).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change BoundarySerial.leftInsert _ _ ((pair H _ false).ports _) = _
  rw [pair_input_left,Combined.left_input]

theorem retained_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (retained T H).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp at *;omega⟩ := by
  change BoundarySerial.leftInsert _ _ ((pair H _ true).ports _) = _
  rw [pair_input_right,Combined.left_input]

theorem second_input : (second T H).ports (.input 0) = .input ⟨1,by simp⟩ := by
  dsimp only [second,Occurrence.comp,Function.comp_apply,
    BoxPullWeakening.RetainedCopy.copyComponent,BoxPullWeakening.RetainedCopy.targetCast,
    Occurrence.ParallelJoin.component,BoxPullWeakening.ReverseComponents.serialLeft,
    MatchEmbedding.occurrence,MatchEmbedding.serialLeft]
  change (retained T H).ports (BoundarySerial.leftInsert _ _
    (CopyRule.pairInsert (CopyRule.residualTree T) H false (.input (0 : Fin 1)))) = _
  rw [CopyRule.pair_left_input,Combined.left_input,retained_input]

theorem tree_input (i : Fin (List.replicate n Wire.term).length) :
    (tree T H).ports (.input i) = .input ⟨i.val+2,by have := i.isLt; simp at *;omega⟩ := by
  change (retained T H).ports (BoundarySerial.leftInsert _ _
    (CopyRule.pairInsert _ _ true (BoundarySerial.leftInsert _ _ (.input i)))) = _
  rw [Combined.left_input,CopyRule.pair_right_input,Combined.left_input,retained_input]

theorem tree_output : (tree T H).ports (.output 0) = (third T H).ports (.input 0) := by
  apply congrArg (remaining T H).ports
  exact BoxPullWeakening.ReverseComponents.serial_boundary _ _ _

end Hypernets.Copying.CopyingDouble.Components
