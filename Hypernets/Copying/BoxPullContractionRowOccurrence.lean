import Hypernets.Copying.BoxPullContractionCopyRows
import Hypernets.Copying.BoxPullWeakeningCopyInjection
import Hypernets.Copying.PrimitiveContextOccurrence

/-! The four-input contraction interchange occurs in the actual original
copying reduct, with both copied contractions and the selected distributor row. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1))
  (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

/-- The literal contraction written with explicit boundary maps, eliminating
only the proof casts in the public definition. -/
abbrev merged := (merge s (H.reboundary rfl (two_interface s k h))).reboundary
  rfl (one_interface s k h)

theorem merged_eq : merged s H = contract s H := (contract_eq s H).symm

@[reducible] def outerEdge : (merged s H).Edge := by
  cases d <;> exact ⟨true,(0 : Fin 1)⟩

theorem outer_label : (merged s H).edgeLabel (outerEdge s H) = primitiveLabel d (.contraction s) := by
  cases d <;> rfl

/-- The displayed contraction is its actual complete primitive corolla. -/
noncomputable def outer : Occurrence (primitiveNet d (.contraction s)) (merged s H) :=
  Occurrence.primitive _ _ (outer_label s H)

def selectedOutput : Fin (environmentInterface (variables s k 1) (atoms s h 1)).length :=
  ⟨k,by clear T H; cases s <;> simp [variables,atoms,environmentInterface] <;> omega⟩

theorem outer_target : (merged s H).target (outerEdge s H) = [.output (selectedOutput s)] := by
  cases d
  all_goals
    change (List.map (Port.cast rfl (one_interface s k h))
    ((merge s (H.reboundary rfl (two_interface s k h))).target
      (contractionEdge s (H.reboundary rfl (two_interface s k h))))) = _
    rw [merge_contraction_target,List.map_singleton]
    apply congrArg List.singleton
    apply congrArg Port.output
    apply Fin.ext
    simp [Port.cast,selectedOutput]

theorem outer_output (i : Fin 1) : (outer s H).ports (.output i) = .output (selectedOutput s) := by
  have eq : i = 0 := Subsingleton.elim _ _
  subst i
  rw [outer,Occurrence.primitive_output]
  simp [Net.targetPort,outer_target]

/-- The original selected row lies in the actual copied environment forest. -/
def selected : Occurrence (CanonicalTree.atDepth s 2 d)
    (Translation.environmentDistributor d (variables s k 1) (atoms s h 1) 2) := by
  clear T H
  cases s
  · exact BoxPullWeakening.CopyRow.termOccurrence d (k+1) h ⟨k,by omega⟩
  · exact BoxPullWeakening.CopyRow.atomOccurrence d k (1+h) ⟨0,by omega⟩

def row : Occurrence (CanonicalTree.atDepth s 2 d) (CopyRule.after T (merged s H)) :=
  (selected (d := d) (k := k) (h := h) s).comp (Occurrence.serialRight _ _)

/-- Select the actual active or retained copy of the output contraction. -/
noncomputable def copied (b : Bool) : Occurrence (primitiveNet d (.contraction s))
    (CopyRule.after T (merged s H)) :=
  (match b with
  | false => (outer s H).comp (BoxPullWeakening.RetainedCopy.copyComponent T (merged s H) false)
  | true => ((outer s H).comp (Occurrence.serialRight _ _)).comp
      (BoxPullWeakening.RetainedCopy.copyComponent T (merged s H) true)).comp
        (BoxPullWeakening.RetainedCopy.serialLeftOccurrence _ _)

theorem copied_disjoint : ∀ a b, a ≠ b → ∀ e c,
    (copied T s H a).edges e ≠ (copied T s H b).edges c := by
  cases d <;> intro a b ne e c eq <;> cases a <;> cases b
  all_goals first | exact ne rfl | cases eq

theorem copied_row_disjoint (b : Bool) (e : (primitiveNet d (.contraction s)).Edge)
    (c : (CanonicalTree.atDepth s 2 d).Edge) :
    (copied T s H b).edges e ≠ (row T s H).edges c := by
  cases d <;> cases b <;> cases s <;> intro eq <;> cases eq

/-- The two copied contractions retain their original left/right order. -/
noncomputable def pairOccurrence :
    Occurrence (Net.Tensor.net (primitiveNet d (.contraction s)) (primitiveNet d (.contraction s)))
      (CopyRule.after T (merged s H)) :=
  Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (primitiveNet d (.contraction s)) (primitiveNet d (.contraction s)))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => match b with | false => copied T s H false | true => copied T s H true) (by
      intro a b ne e c
      cases a <;> cases b
      all_goals first | exact False.elim (ne rfl) | exact copied_disjoint T s H _ _ ne _ _)

theorem copied_output (b : Bool) (i : Fin 1) :
    (copied T s H b).ports (.output i) =
      .internal (.inl (CopyRule.copyOutput (variables s k 1) (atoms s h 1) b (selectedOutput s))) := by
  cases b
  · change BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) false
      ((outer s H).ports (.output i))) = _
    rw [outer_output,CopyRule.pair_output,CopyRule.serial_left_output]
  · change BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) true
      (BoundarySerial.rightInsert _ _ ((outer s H).ports (.output i)))) = _
    rw [outer_output,Application.right_serial_output,CopyRule.pair_output,CopyRule.serial_left_output]

/-- The selected row's inputs are the two copied images of the contracted
resource, in the original active/retained order. -/
theorem selected_input (b : Bool) :
    (selected (d := d) (k := k) (h := h) s).ports
      (.input (if b then ⟨1,by simp⟩ else ⟨0,by simp⟩)) =
      .input (CopyRule.copyOutput (variables s k 1) (atoms s h 1) b (selectedOutput s)) := by
  rw [BoxPullWeakening.RetainedCopy.copyOutput_eq]
  cases s
  · change _ = Port.input (PairBoundary.index (h := h) b
      (EnvironmentPermutation.termIndex (⟨k,by omega⟩ : Fin (k+1))))
    rw [PairBoundary.term_index]
    cases b <;> apply congrArg Port.input <;> apply Fin.ext <;>
      simp [selected,BoxPullWeakening.CopyRow.termOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,
        Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
        Distributor.boundary,Distributor.inputIndex,FinGrid.index,EnvironmentPermutation.termIndex,PairBoundary.use]
  · change _ = Port.input (PairBoundary.index (k := k) b
      (EnvironmentPermutation.atomIndex (⟨0,by omega⟩ : Fin (1+h))))
    rw [PairBoundary.atom_index]
    cases b <;> apply congrArg Port.input <;> apply Fin.ext <;>
      simp [selected,BoxPullWeakening.CopyRow.atomOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,
        Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
        Distributor.boundary,Distributor.inputIndex,FinGrid.index,EnvironmentPermutation.atomIndex,PairBoundary.use]

theorem pair_boundary (i : Fin 2) :
    (pairOccurrence T s H).ports (.output i) = (row T s H).ports (.input i) := by
  have casesI : i = 0 ∨ i = 1 := by
    by_cases z : i.val = 0
    · exact .inl (Fin.ext z)
    · exact .inr (Fin.ext (by have := i.isLt; omega))
  rcases casesI with rfl | rfl
  · change (copied T s H false).ports (.output (0 : Fin 1)) =
      BoundarySerial.rightInsert _ _ ((selected (d := d) (k := k) (h := h) s).ports (.input ⟨0,by simp⟩))
    have law := selected_input (d := d) (k := k) (h := h) s false
    simp only [Bool.false_eq_true,ite_false] at law
    rw [copied_output,law,CopyRule.serial_right_input]
  · change (copied T s H true).ports (.output (0 : Fin 1)) =
      BoundarySerial.rightInsert _ _ ((selected (d := d) (k := k) (h := h) s).ports (.input ⟨1,by simp⟩))
    have law := selected_input (d := d) (k := k) (h := h) s true
    simp only [ite_true] at law
    rw [copied_output,law,CopyRule.serial_right_input]

/-- The actual five-edge inside row has a complete ordered occurrence in
this precise copying reduct. -/
noncomputable def insideOccurrence : Occurrence (inside d s) (CopyRule.after T (merged s H)) :=
  Occurrence.SerialJoin.occurrence (pairOccurrence T s H) (row T s H)
    (pair_boundary T s H) (by
      cases d <;> rintro ⟨b,e⟩ c <;> cases b
      all_goals first
        | exact copied_row_disjoint T s H false e c
        | exact copied_row_disjoint T s H true e c)

/-- The row also occurs in the public literal reduct; the change above was
only removal of proof casts on the ordered boundary. -/
noncomputable def originalOccurrence : Occurrence (inside d s) (CopyRule.after T (contract s H)) := by
  rw [← merged_eq s H]
  exact insideOccurrence T s H

/-- The actual whole-graph intermediate with the seven-edge outside row
plugged into the computed finite complement of the five-edge inside row. -/
noncomputable def corrected := CompleteMatchCut.replaceWith
  (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label (outside d s)

theorem merged_free (free : FocusFree H) : FocusFree (merged s H) := by
  exact (merge_allLabels _ s (H.reboundary rfl (two_interface s k h))).mpr
    ⟨free,by intro m eq; cases eq⟩

theorem cut_free (free : FocusFree H) :
    FocusFree (CompleteMatchCut.net (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label) := by
  intro e
  cases e with
  | none => cases d <;> intro m eq <;> cases eq
  | some e => exact CopyRule.focusFree_after T _ (merged_free s H free) e.val

/-- One genuine sharing-tree filling witness performs this exact local
interchange inside the complete original copying reduct. -/
noncomputable def correction (free : FocusFree H) :
    FillingWitness SharingTreeAlgebra.template (CopyRule.after T (merged s H)) (corrected T s H) :=
  (((FillingWitness.of_rel 0 (pair d s)).reboundary
    (CompleteMatchCut.hole_input (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm
    (CompleteMatchCut.hole_output (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm).plug
      (CompleteMatchCut.net (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label)
      (cut_free T s H free) none).congr
        (CompleteMatchCut.realization (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label)
        (DeepIso.refl _)

end Hypernets.Copying.BoxPullContraction.CopyRows
