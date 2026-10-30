import Hypernets.Copying.BoxPullContractionCopyReconstruction

/-! The complete outside-contraction occurrence fixes the actual ordered
external interface of the original copying reduct. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

theorem retainedBranch_input (i : Fin (List.replicate n Wire.term).length) :
    (retainedBranch T s H).ports (.input i) = .input i := by
  unfold retainedBranch
  rw [Occurrence.SerialJoin.occurrence_input]
  exact Combined.left_input _ _ i

theorem copies_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (copies T s H).ports (.input i) = .input i := by
  by_cases zero : i.val = 0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have law := copies_component T s H false (.input (0 : Fin 1))
    rw [CopyRule.pair_left_input] at law
    change (copies T s H).ports _ = CopyRule.pairInsert T (merged s H) false ((payload s H).ports (.input 0)) at law
    rw [payload_input,CopyRule.pair_left_input] at law
    exact law
  · let j : Fin (List.replicate n Wire.term).length := ⟨i.val-1,by have := i.isLt; simp at *; omega⟩
    have eq : i = ⟨j.val+1,by have := j.isLt; simp at *; omega⟩ := Fin.ext (by dsimp [j]; omega)
    have law := copies_component T s H true (.input j)
    rw [CopyRule.pair_right_input] at law
    change (copies T s H).ports _ = CopyRule.pairInsert T (merged s H) true ((retainedBranch T s H).ports (.input j)) at law
    rw [retainedBranch_input,CopyRule.pair_right_input] at law
    exact eq ▸ law

theorem originalCopies_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (originalCopies T s H).ports (.input i) = .input i := by
  change BoundarySerial.leftInsert _ _ ((copies T s H).ports (.input i)) = _
  rw [copies_input,Combined.left_input]

theorem correctedCopies_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (correctedCopies T s H).ports (.input i) = .input i := by
  have cut : Occurrence.cutPort (insideOccurrence T s H) (originalCopies T s H)
      (originalCopies_disjoint T s H) (.input i) = .input i := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_project _ _ _).trans (originalCopies_input T s H i)
  let C := CompleteMatchCut.net (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label
  let R := (outside d s).reboundary
    (CompleteMatchCut.hole_input (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm
    (CompleteMatchCut.hole_output (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm
  change Net.Replacement.host C none R (Occurrence.cutPort (insideOccurrence T s H)
    (originalCopies T s H) (originalCopies_disjoint T s H) (.input i)) = _
  rw [cut]
  rfl

theorem after_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (afterOccurrence T s H).ports (.input i) = .input i := by
  rw [afterOccurrence,Occurrence.SerialJoin.occurrence_input,correctedCopies_input]

/-- Every surviving component preserves a boundary output already external
in the original host of the sharing-row cut. -/
theorem retained_output {J K} {A : Hypernet d J K}
    (g : Occurrence A (CopyRule.after T (merged s H)))
    (disjoint : ∀ a b, (insideOccurrence T s H).edges a ≠ g.edges b)
    (v : A.Vertex) (i : Fin (environmentInterface (variables s k 1) (atoms s h 1)).length)
    (link : g.ports v = .output i) :
    ((insideOccurrence T s H).acrossCut g disjoint (outside d s)).ports v = .output i := by
  have cut : Occurrence.cutPort (insideOccurrence T s H) g disjoint v = .output i := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_project _ _ _).trans link
  let C := CompleteMatchCut.net (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label
  let R := (outside d s).reboundary
    (CompleteMatchCut.hole_input (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm
    (CompleteMatchCut.hole_output (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm
  change Net.Replacement.host C none R (Occurrence.cutPort (insideOccurrence T s H) g disjoint v) = _
  rw [cut]
  rfl

theorem originalTermRow_output (i : Fin (variables s k 1)) :
    (originalTermRow T s H i).ports (.output ⟨0,by simp⟩) =
      .output (EnvironmentPermutation.termIndex i) := by
  change BoundarySerial.rightInsert _ _ (.output _) = _
  rw [Application.right_serial_output]
  rfl

theorem originalAtomRow_output (i : Fin (atoms s h 1)) :
    (originalAtomRow T s H i).ports (.output ⟨0,by simp⟩) =
      .output (EnvironmentPermutation.atomIndex i) := by
  change BoundarySerial.rightInsert _ _ (.output _) = _
  rw [Application.right_serial_output]
  apply congrArg Port.output
  apply Fin.ext
  simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,
    EnvironmentPermutation.atomIndex]

theorem retainedTermRow_output (i : Fin (variables s k 1)) (unselected : s = .term → i.val ≠ k) :
    (retainedTermRow T s H i unselected).ports (.output ⟨0,by simp⟩) =
      .output (EnvironmentPermutation.termIndex i) :=
  retained_output T s H _ _ _ _ (originalTermRow_output T s H i)

theorem retainedAtomRow_output (i : Fin (atoms s h 1)) (unselected : s = .atom → i.val ≠ 0) :
    (retainedAtomRow T s H i unselected).ports (.output ⟨0,by simp⟩) =
      .output (EnvironmentPermutation.atomIndex i) :=
  retained_output T s H _ _ _ _ (originalAtomRow_output T s H i)

/-- All unselected outputs keep the exact original compressed ordering. -/
theorem after_unselected_output
    (i : Fin (environmentInterface (variables s k 2) (atoms s h 2)).length)
    (away : i.val < k ∨ k+2 ≤ i.val) :
    (afterOccurrence T s H).ports (.output i) = .output (collapsedOutput s i) := by
  rw [afterOccurrence,Occurrence.SerialJoin.occurrence_output]
  by_cases isTerm : i.val < variables s k 2
  · let j : Fin (variables s k 2) := ⟨i.val,isTerm⟩
    have eq : i = EnvironmentPermutation.termIndex (h := atoms s h 2) j := rfl
    rw [eq,distributor_term_output]
    cases s
    · have before : j.val < k := by
        change i.val < k
        change i.val < k+2 at isTerm
        omega
      simp only [termRow,dite_eq_left before]
      rw [retainedTermRow_output]
      apply congrArg Port.output
      apply Fin.ext
      simp [collapsedOutput,EnvironmentPermutation.termIndex,before]
    · change (retainedTermRow T .atom H j (by intro eq; cases eq)).ports _ = _
      rw [retainedTermRow_output]
      apply congrArg Port.output
      apply Fin.ext
      have before : j.val < k := isTerm
      simp [collapsedOutput,EnvironmentPermutation.termIndex,before]
  · let j : Fin (atoms s h 2) := ⟨i.val-variables s k 2,by have := i.isLt; simp [environmentInterface] at this; omega⟩
    have eq : i = EnvironmentPermutation.atomIndex (k := variables s k 2) j :=
      Fin.ext (by dsimp [j,EnvironmentPermutation.atomIndex]; omega)
    rw [eq,distributor_atom_output]
    cases s
    · change (retainedAtomRow T .term H j (by intro eq; cases eq)).ports _ = _
      rw [retainedAtomRow_output]
      apply congrArg Port.output
      apply Fin.ext
      have before : ¬ k+2+j.val < k := by omega
      simp [collapsedOutput,EnvironmentPermutation.atomIndex,variables,before]
    · have selected : ¬ j.val < 2 := by
        have jt : i.val = k+j.val := congrArg Fin.val eq
        omega
      simp only [atomRow,dite_eq_right selected]
      rw [retainedAtomRow_output]
      apply congrArg Port.output
      apply Fin.ext
      have before : ¬ k+j.val < k := by omega
      simp [collapsedOutput,EnvironmentPermutation.atomIndex,variables,before]
      omega

/-- The selected inside row ends at the original contracted output. -/
theorem original_row_output (i : Fin 1) :
    (insideOccurrence T s H).ports (.output i) = .output (selectedOutput s) := by
  have zero : i = 0 := Subsingleton.elim _ _
  subst i
  rw [insideOccurrence,Occurrence.SerialJoin.occurrence_output]
  change BoundarySerial.rightInsert _ _ ((selected (d := d) (k := k) (h := h) s).ports (.output ⟨0,by simp⟩)) = _
  cases s
  all_goals
    change BoundarySerial.rightInsert _ _ (.output _) = _
    rw [Application.right_serial_output]
    apply congrArg Port.output
    apply Fin.ext
    simp [selected,selectedOutput,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary]

/-- The inserted outside contraction keeps the actual original output port. -/
theorem insertedContraction_output (i : Fin 1) :
    (insertedContraction T s H).ports (.output i) = .output (selectedOutput s) := by
  change (inserted T s H).ports (BoundarySerial.rightInsert _ _ (.output i)) = _
  rw [Application.right_serial_output]
  change Net.Replacement.host _ none _
    ((CompleteMatchCut.net (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).targetPort none
      (Fin.cast (congrArg List.length
        (CompleteMatchCut.hole_output (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm) i)) = _
  rw [CompleteMatchCut.hole_targetPort]
  have cut : CompleteMatchCut.outputPort (insideOccurrence T s H).matchEmbedding i = .output (selectedOutput s) := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_output (insideOccurrence T s H).matchEmbedding i).trans (original_row_output T s H i)
  rw [cut]
  rfl

private theorem occurrence_cast_input {r I O J K} {A B : Hypernet r I O} {C : Hypernet r J K}
    (eq : A = B) (f : Occurrence B C) (i : Fin I.length) :
    ((congrArg (fun X => Occurrence X C) eq).mpr f).ports (.input i) = f.ports (.input i) := by cases eq; rfl

private theorem occurrence_cast_output {r I O J K} {A B : Hypernet r I O} {C : Hypernet r J K}
    (eq : A = B) (f : Occurrence B C) (i : Fin O.length) :
    ((congrArg (fun X => Occurrence X C) eq).mpr f).ports (.output i) = f.ports (.output i) := by cases eq; rfl

/-- The normalization fixes every original ordered input, including all
unused residual-tree inputs. -/
theorem normalization_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (normalizationOccurrence T s H).ports (.input i) = .input i := by
  unfold normalizationOccurrence
  rw [occurrence_cast_input (contract_eq s (CopyRule.after T H))]
  change (afterOccurrence T s H).ports (.input i) = _
  exact after_input T s H i

/-- The normalization fixes the complete ordered contracted environment. -/
theorem normalization_output
    (i : Fin (environmentInterface (variables s k 1) (atoms s h 1)).length) :
    (normalizationOccurrence T s H).ports (.output i) = .output i := by
  unfold normalizationOccurrence
  rw [occurrence_cast_output (contract_eq s (CopyRule.after T H))]
  change Occurrence.MergeJoin.host
    ((afterOccurrence T s H).reboundarySource rfl (two_interface s k h))
    (insertedContraction T s H) (.output (Fin.cast (congrArg List.length (one_interface s k h)).symm i)) = _
  by_cases before : i.val < k
  · have before' : i.val < (List.replicate k Wire.term).length := by simpa using before
    simp only [Occurrence.MergeJoin.host,Fin.val_cast,before',↓reduceDIte]
    change (afterOccurrence T s H).ports (.output ⟨i.val,by
      have := i.isLt; cases s <;> simp [variables,atoms,environmentInterface] at * <;> omega⟩) = _
    rw [after_unselected_output T s H _ (.inl before)]
    apply congrArg Port.output
    apply Fin.ext
    simp [collapsedOutput,before]
  · by_cases selected : i.val = k
    · have before' : ¬ i.val < (List.replicate k Wire.term).length := by simpa using before
      have selected' : i.val = (List.replicate k Wire.term).length := by simpa using selected
      simp only [Occurrence.MergeJoin.host,Fin.val_cast,before',selected',↓reduceDIte]
      rw [insertedContraction_output]
      simp only [Nat.lt_irrefl,↓reduceDIte]
      apply congrArg Port.output
      exact Fin.ext selected.symm
    · have before' : ¬ i.val < (List.replicate k Wire.term).length := by simpa using before
      have selected' : ¬ i.val = (List.replicate k Wire.term).length := by simpa using selected
      simp only [Occurrence.MergeJoin.host,Fin.val_cast,before',selected',↓reduceDIte]
      change (afterOccurrence T s H).ports (.output ⟨i.val+1,by
        have := i.isLt; cases s <;> simp [variables,atoms,environmentInterface] at * <;> omega⟩) = _
      have away : k+2 ≤ i.val+1 := by omega
      rw [after_unselected_output T s H _ (.inr away)]
      apply congrArg Port.output
      apply Fin.ext
      have later : ¬ i.val+1 < k := by omega
      simp [collapsedOutput,later]

end Hypernets.Copying.BoxPullContraction.CopyRows
