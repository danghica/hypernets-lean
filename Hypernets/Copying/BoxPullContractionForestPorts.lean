import Hypernets.Copying.BoxPullContractionForest

/-! Exact ordered port coordinates for every reconstructed resource row. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening

/-- A term row receives active and retained uses in the original copy-major order. -/
theorem termOccurrence_input (d k h : Nat) (i : Fin k) (b : Bool) :
    (BoxPullWeakening.CopyRow.termOccurrence d k h i).ports
      (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) =
      .input (CopyRule.copyOutput k h b (EnvironmentPermutation.termIndex i)) := by
  rw [BoxPullWeakening.RetainedCopy.copyOutput_eq,PairBoundary.term_index]
  cases b <;> apply congrArg Port.input <;> apply Fin.ext <;>
    simp [BoxPullWeakening.CopyRow.termOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,
      Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
      Distributor.boundary,Distributor.inputIndex,FinGrid.index,EnvironmentPermutation.termIndex,PairBoundary.use]

theorem atomOccurrence_input (d k h : Nat) (i : Fin h) (b : Bool) :
    (BoxPullWeakening.CopyRow.atomOccurrence d k h i).ports
      (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) =
      .input (CopyRule.copyOutput k h b (EnvironmentPermutation.atomIndex i)) := by
  rw [BoxPullWeakening.RetainedCopy.copyOutput_eq,PairBoundary.atom_index]
  cases b <;> apply congrArg Port.input <;> apply Fin.ext <;>
    simp [BoxPullWeakening.CopyRow.atomOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,
      Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
      Distributor.boundary,Distributor.inputIndex,FinGrid.index,EnvironmentPermutation.atomIndex,PairBoundary.use]

variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

theorem originalTermRow_input (i : Fin (variables s k 1)) (b : Bool) :
    (originalTermRow T s H i).ports (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) =
      .internal (.inl (CopyRule.copyOutput (variables s k 1) (atoms s h 1) b (EnvironmentPermutation.termIndex i))) := by
  change BoundarySerial.rightInsert _ _ ((BoxPullWeakening.CopyRow.termOccurrence _ _ _ i).ports _) = _
  rw [termOccurrence_input,CopyRule.serial_right_input]

theorem originalAtomRow_input (i : Fin (atoms s h 1)) (b : Bool) :
    (originalAtomRow T s H i).ports (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) =
      .internal (.inl (CopyRule.copyOutput (variables s k 1) (atoms s h 1) b (EnvironmentPermutation.atomIndex i))) := by
  change BoundarySerial.rightInsert _ _ ((BoxPullWeakening.CopyRow.atomOccurrence _ _ _ i).ports _) = _
  rw [atomOccurrence_input,CopyRule.serial_right_input]

/-- Every reconstructed term row connects to the original selected copy wire. -/
theorem termRow_input (i : Fin (variables s k 2)) (b : Bool) :
    (correctedCopies T s H).ports (.output
      (CopyRule.copyOutput (variables s k 2) (atoms s h 2) b (EnvironmentPermutation.termIndex i))) =
      (termRow T s H i).ports (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) := by
  cases s
  · by_cases before : i.val < k
    · simp only [termRow,dite_eq_left before]
      apply Occurrence.acrossCut_link
      rw [originalTermRow_input,originalCopies_unselected T .term H b _ (.inl before)]
      congr 3
      apply Fin.ext
      simp [collapsedOutput,EnvironmentPermutation.termIndex,before]
    · simp only [termRow,dite_eq_right before]
      have bound := i.isLt
      change i.val < k+2 at bound
      have eq : EnvironmentPermutation.termIndex (h := h) i = resource (k := k) (h := h) .term
          ⟨i.val-k,by omega⟩ := Fin.ext (by simp [resource,EnvironmentPermutation.termIndex]; omega)
      rw [eq]
      exact corrected_selected_link T .term H _ b
  · change (correctedCopies T .atom H).ports _ =
      (retainedTermRow T .atom H i (by intro eq; cases eq)).ports _
    apply Occurrence.acrossCut_link
    have bound := i.isLt
    change i.val < k at bound
    rw [originalTermRow_input,originalCopies_unselected T .atom H b _ (.inl bound)]
    congr 3
    apply Fin.ext
    simp [collapsedOutput,EnvironmentPermutation.termIndex,bound]

/-- Every reconstructed atom row uses the same original copy-major boundary. -/
theorem atomRow_input (i : Fin (atoms s h 2)) (b : Bool) :
    (correctedCopies T s H).ports (.output
      (CopyRule.copyOutput (variables s k 2) (atoms s h 2) b (EnvironmentPermutation.atomIndex i))) =
      (atomRow T s H i).ports (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) := by
  cases s
  · change (correctedCopies T .term H).ports _ =
      (retainedAtomRow T .term H i (by intro eq; cases eq)).ports _
    apply Occurrence.acrossCut_link
    have away : k+2 ≤ (EnvironmentPermutation.atomIndex (k := k+2) i).val := by
      simp [EnvironmentPermutation.atomIndex]
    rw [originalAtomRow_input,originalCopies_unselected T .term H b _ (.inr away)]
    congr 3
    apply Fin.ext
    simp [collapsedOutput,EnvironmentPermutation.atomIndex,variables]
    omega
  · by_cases selected : i.val < 2
    · simp only [atomRow,dite_eq_left selected]
      have eq : EnvironmentPermutation.atomIndex (k := k) i = resource (k := k) (h := h) .atom
          ⟨i.val,selected⟩ := Fin.ext rfl
      rw [eq]
      exact corrected_selected_link T .atom H _ b
    · simp only [atomRow,dite_eq_right selected]
      apply Occurrence.acrossCut_link
      have away : k+2 ≤ (EnvironmentPermutation.atomIndex (k := k) i).val := by
        simp only [EnvironmentPermutation.atomIndex]
        omega
      rw [originalAtomRow_input,originalCopies_unselected T .atom H b _ (.inr away)]
      congr 3
      apply Fin.ext
      have before : ¬ k+i.val < k := by omega
      simp [collapsedOutput,EnvironmentPermutation.atomIndex,variables,before]
      omega

end Hypernets.Copying.BoxPullContraction.CopyRows
