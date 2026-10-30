import Hypernets.Copying.BoxPullContractionForestAssembly
import Hypernets.Copying.BoxPullContractionMergeJoin
import Hypernets.Copying.OccurrenceCoverIso

/-! Reassemble the actual original copy reduct from the retained copies and
all reconstructed resource rows after BPullC's sharing interchange. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

theorem termForest_port (i : Fin (variables s k 2)) (v : (CanonicalTree.atDepth .term 2 d).Vertex) :
    (termForest T s H).ports ((BoxPullWeakening.CopyRow.forestOccurrence .term (variables s k 2) 2 d i).ports v) =
      (termRow T s H i).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _ (Port.map id _) = _
  simp only [Port.map_id_fun,id_eq]
  have same : (BoxPullWeakening.CopyRow.forestOccurrence .term (variables s k 2) 2 d i).ports v =
      Net.Parallel.embed (fun _ : Fin (variables s k 2) => CanonicalTree.atDepth .term 2 d)
        (Distributor.boundary .term (variables s k 2) 2) i v := by cases v <;> rfl
  rw [same,Occurrence.ParallelJoin.embed_ports]

theorem atomForest_port (i : Fin (atoms s h 2)) (v : (CanonicalTree.atDepth .atom 2 d).Vertex) :
    (atomForest T s H).ports ((BoxPullWeakening.CopyRow.forestOccurrence .atom (atoms s h 2) 2 d i).ports v) =
      (atomRow T s H i).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _ (Port.map id _) = _
  simp only [Port.map_id_fun,id_eq]
  have same : (BoxPullWeakening.CopyRow.forestOccurrence .atom (atoms s h 2) 2 d i).ports v =
      Net.Parallel.embed (fun _ : Fin (atoms s h 2) => CanonicalTree.atDepth .atom 2 d)
        (Distributor.boundary .atom (atoms s h 2) 2) i v := by cases v <;> rfl
  rw [same,Occurrence.ParallelJoin.embed_ports]

theorem distributor_term_port (i : Fin (variables s k 2)) (v : (CanonicalTree.atDepth .term 2 d).Vertex) :
    (distributor T s H).ports ((BoxPullWeakening.CopyRow.termOccurrence d (variables s k 2) (atoms s h 2) i).ports v) =
      (termRow T s H i).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Net.Parallel.embed (Net.Tensor.family _ _) (Net.Tensor.boundary _ _ _ _) false
      ((BoxPullWeakening.CopyRow.forestOccurrence .term (variables s k 2) 2 d i).ports v)) = _
  rw [Occurrence.ParallelJoin.embed_ports]
  exact termForest_port T s H i v

theorem distributor_atom_port (i : Fin (atoms s h 2)) (v : (CanonicalTree.atDepth .atom 2 d).Vertex) :
    (distributor T s H).ports ((BoxPullWeakening.CopyRow.atomOccurrence d (variables s k 2) (atoms s h 2) i).ports v) =
      (atomRow T s H i).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Net.Parallel.embed (Net.Tensor.family _ _) (Net.Tensor.boundary _ _ _ _) true
      ((BoxPullWeakening.CopyRow.forestOccurrence .atom (atoms s h 2) 2 d i).ports v)) = _
  rw [Occurrence.ParallelJoin.embed_ports]
  exact atomForest_port T s H i v

/-- Every original serial junction between the pair of copies and its resource
forest remains literally attached after the selected-row replacement. -/
theorem after_boundary (i : Fin (environmentInterface (variables s k 2*2) (atoms s h 2*2)).length) :
    (correctedCopies T s H).ports (.output i) = (distributor T s H).ports (.input i) := by
  obtain ⟨b,j,rfl⟩ := PairBoundary.index_surjective i
  rw [← BoxPullWeakening.RetainedCopy.copyOutput_eq]
  by_cases term : j.val < variables s k 2
  · let a : Fin (variables s k 2) := ⟨j.val,term⟩
    have eq : j = EnvironmentPermutation.termIndex (h := atoms s h 2) a := rfl
    rw [eq,termRow_input]
    have law := distributor_term_port T s H a (.input ⟨if b then 1 else 0,by cases b <;> simp⟩)
    rw [termOccurrence_input] at law
    exact law.symm
  · let a : Fin (atoms s h 2) := ⟨j.val-variables s k 2,by have := j.isLt; simp [environmentInterface] at this; omega⟩
    have eq : j = EnvironmentPermutation.atomIndex (k := variables s k 2) a :=
      Fin.ext (by dsimp [a,EnvironmentPermutation.atomIndex]; omega)
    rw [eq,atomRow_input]
    have law := distributor_atom_port T s H a (.input ⟨if b then 1 else 0,by cases b <;> simp⟩)
    rw [atomOccurrence_input] at law
    exact law.symm

theorem copies_term_disjoint (i : Fin (variables s k 2)) (e : (CopyRule.copies T H).Edge)
    (a : (CanonicalTree.atDepth .term 2 d).Edge) :
    (correctedCopies T s H).edges e ≠ (termRow T s H i).edges a := by
  intro eq
  cases s
  · by_cases before : i.val < k
    · simp only [termRow,dite_eq_left before] at eq
      cases d <;> cases eq
    · simp only [termRow,dite_eq_right before] at eq
      cases d <;> cases eq
  · cases d <;> cases eq

theorem copies_atom_disjoint (i : Fin (atoms s h 2)) (e : (CopyRule.copies T H).Edge)
    (a : (CanonicalTree.atDepth .atom 2 d).Edge) :
    (correctedCopies T s H).edges e ≠ (atomRow T s H i).edges a := by
  intro eq
  cases s
  · cases d <;> cases eq
  · by_cases selected : i.val < 2
    · simp only [atomRow,dite_eq_left selected] at eq
      cases d <;> cases eq
    · simp only [atomRow,dite_eq_right selected] at eq
      cases d <;> cases eq

theorem after_disjoint : ∀ e c, (correctedCopies T s H).edges e ≠ (distributor T s H).edges c := by
  intro e c eq
  rcases c with ⟨b,c⟩
  cases b
  · rcases c with ⟨i,c⟩
    exact copies_term_disjoint T s H i e c eq
  · rcases c with ⟨i,c⟩
    exact copies_atom_disjoint T s H i e c eq

/-- The full original uncontracted copy reduct has its complete occurrence
inside the actual corrected graph. Its two selected outputs feed the sole
external contraction, reconstructed separately below. -/
noncomputable def afterOccurrence : Occurrence (CopyRule.after T H) (corrected T s H) :=
  Occurrence.SerialJoin.occurrence (correctedCopies T s H) (distributor T s H)
    (after_boundary T s H) (after_disjoint T s H)

noncomputable def insertedContraction : Occurrence (primitiveNet d (.contraction s)) (corrected T s H) :=
  (Occurrence.serialRight (Distributor.atDepth s 2 2 d) (primitiveNet d (.contraction s))).comp (inserted T s H)

theorem insertedRow_output (j : Fin 2) :
    (insertedRow T s H j).ports (.output ⟨0,by simp⟩) = (insertedContraction T s H).ports (.input j) := by
  change (inserted T s H).ports (BoundarySerial.leftInsert _ _
    ((BoxPullWeakening.CopyRow.forestOccurrence s 2 2 d j).ports (.output ⟨0,by simp⟩))) =
      (inserted T s H).ports (BoundarySerial.rightInsert _ _ (.input j))
  change (inserted T s H).ports (BoundarySerial.leftInsert _ _ (.output j)) = _
  rw [CopyRule.serial_left_output,CopyRule.serial_right_input]

theorem distributor_term_output (i : Fin (variables s k 2)) :
    (distributor T s H).ports (.output (EnvironmentPermutation.termIndex i)) =
      (termRow T s H i).ports (.output ⟨0,by simp⟩) :=
  distributor_term_port T s H i (.output ⟨0,by simp⟩)

theorem distributor_atom_output (i : Fin (atoms s h 2)) :
    (distributor T s H).ports (.output (EnvironmentPermutation.atomIndex i)) =
      (atomRow T s H i).ports (.output ⟨0,by simp⟩) := by
  simpa only [BoxPullWeakening.CopyRow.atomOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,
    Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
    Distributor.boundary,EnvironmentPermutation.atomIndex,List.length_replicate] using
    distributor_atom_port T s H i (.output ⟨0,by simp⟩)

/-- The reconstructed selected outputs meet the two original ordered inputs
of the sole outside contraction. -/
theorem after_selected_output (j : Fin 2) :
    (afterOccurrence T s H).ports (.output (resource s j)) =
      (insertedContraction T s H).ports (.input j) := by
  rw [afterOccurrence,Occurrence.SerialJoin.occurrence_output]
  cases s
  · change (distributor T .term H).ports (.output (EnvironmentPermutation.termIndex
      (⟨k+j.val,by have := j.isLt; change k+j.val < k+2; omega⟩ : Fin (k+2)))) = _
    rw [distributor_term_output]
    have before : ¬ k+j.val < k := by omega
    simp only [termRow,dite_eq_right before]
    have index : (⟨k+j.val-k,by omega⟩ : Fin 2) = j := Fin.ext (by simp)
    rw [index,insertedRow_output]
  · change (distributor T .atom H).ports (.output (EnvironmentPermutation.atomIndex
      (⟨j.val,by have := j.isLt; change j.val < 2+h; omega⟩ : Fin (2+h)))) = _
    rw [distributor_atom_output]
    simp only [atomRow,dite_eq_left j.isLt]
    exact insertedRow_output T .atom H j

theorem after_contraction_disjoint : ∀ e c,
    (afterOccurrence T s H).edges e ≠ (insertedContraction T s H).edges c := by
  cases d
  all_goals
    intro e c eq
    rcases e with ⟨b,e⟩
    cases b
    · cases eq
    · rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨i,e⟩
        change (termRow T s H i).edges e = (insertedContraction T s H).edges c at eq
        cases s
        · by_cases before : i.val < k
          · simp only [termRow,dite_eq_left before] at eq
            cases eq
          · simp only [termRow,dite_eq_right before] at eq
            cases eq
        · cases eq
      · rcases e with ⟨i,e⟩
        change (atomRow T s H i).edges e = (insertedContraction T s H).edges c at eq
        cases s
        · cases eq
        · by_cases selected : i.val < 2
          · simp only [atomRow,dite_eq_left selected] at eq
            cases eq
          · simp only [atomRow,dite_eq_right selected] at eq
            cases eq

/-- Complete occurrence with all interface casts written as explicit boundary
maps; this exposes the original finite carriers for coverage proofs. -/
noncomputable def rawNormalizationOccurrence :
    Occurrence ((merge s ((CopyRule.after T H).reboundary rfl (two_interface s k h))).reboundary
      rfl (one_interface s k h)) (corrected T s H) :=
  (Occurrence.MergeJoin.occurrence
    ((afterOccurrence T s H).reboundarySource rfl (two_interface s k h))
    (insertedContraction T s H) (by
      intro i
      change (afterOccurrence T s H).ports (.output ⟨(List.replicate k Wire.term).length+i.val,by
        have := i.isLt; cases s <;> simp [variables,atoms,environmentInterface] <;> omega⟩) = _
      simpa only [List.length_replicate,resource] using after_selected_output T s H i)
    (after_contraction_disjoint T s H)).reboundarySource rfl (one_interface s k h)


/-- The literal outside-contraction reduct has its complete occurrence in
the computed sharing correction. -/
noncomputable def normalizationOccurrence :
    Occurrence (contract s (CopyRule.after T H)) (corrected T s H) := by
  rw [contract_eq]
  exact rawNormalizationOccurrence T s H

end Hypernets.Copying.BoxPullContraction.CopyRows
