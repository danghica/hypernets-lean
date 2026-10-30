import Hypernets.Copying.CopyingDoubleComponents
import Hypernets.Copying.CopyingDoubleNormal

/-! Complete six-edge resource rows in the two-copy graph, with original
payload-output attachments and no canonical-tree simplification. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble.Components
open Graph Opening
variable {d n k h}

def atomPosition (i : Frame.Resource k h) (atom : ¬i.val < k) : Fin h :=
  ⟨i.val-k,by
    have bound := i.isLt
    simp only [environmentInterface,List.length_append,List.length_replicate] at bound
    omega⟩

/-- The resource position retains its original term/atom sort. -/
def resource (i : Frame.Resource k h) :
    Occurrence (CanonicalTree.atDepth (Frame.sort k h i) 2 d)
      (Translation.environmentDistributor d k h 2) where
  ports v := if term : i.val < k then (BoxPullWeakening.CopyRow.termOccurrence d k h ⟨i.val,term⟩).ports v
    else (BoxPullWeakening.CopyRow.atomOccurrence d k h (atomPosition i term)).ports v
  internals v := if term : i.val < k then (BoxPullWeakening.CopyRow.termOccurrence d k h ⟨i.val,term⟩).internals v
    else (BoxPullWeakening.CopyRow.atomOccurrence d k h (atomPosition i term)).internals v
  edges e := if term : i.val < k then (BoxPullWeakening.CopyRow.termOccurrence d k h ⟨i.val,term⟩).edges e
    else (BoxPullWeakening.CopyRow.atomOccurrence d k h (atomPosition i term)).edges e
  internal_map v := by split <;> rfl
  internal_injective := by
    intro a b eq
    split at eq
    · exact (BoxPullWeakening.CopyRow.termOccurrence d k h _).internal_injective eq
    · exact (BoxPullWeakening.CopyRow.atomOccurrence d k h _).internal_injective eq
  edge_injective := by
    intro a b eq
    split at eq
    · exact (BoxPullWeakening.CopyRow.termOccurrence d k h _).edge_injective eq
    · exact (BoxPullWeakening.CopyRow.atomOccurrence d k h _).edge_injective eq
  internal_label v := by
    by_cases term : i.val < k
    · simp only [dite_eq_left term]
      change Wire.term = (Frame.sort k h i).wire
      simp [Frame.sort,term,ShareSort.wire]
    · simp only [dite_eq_right term]
      change Wire.atom = (Frame.sort k h i).wire
      simp [Frame.sort,term,ShareSort.wire]
  label e := by
    by_cases term : i.val < k
    · simp only [dite_eq_left term]
      change LabelEquiv d _ (primitiveLabel d ((CanonicalTree.net .term 2).edgeLabel e))
      simp only [CanonicalTree.atDepth,Net.relabel,Frame.sort,ite_eq_left term]
      exact labelEquiv_refl _ _
    · simp only [dite_eq_right term]
      change LabelEquiv d _ (primitiveLabel d ((CanonicalTree.net .atom 2).edgeLabel e))
      simp only [CanonicalTree.atDepth,Net.relabel,Frame.sort,ite_eq_right term]
      exact labelEquiv_refl _ _
  source e := by
    by_cases term : i.val < k
    · simp only [dite_eq_left term]
      exact (BoxPullWeakening.CopyRow.termOccurrence d k h _).source e
    · simp only [dite_eq_right term]
      exact (BoxPullWeakening.CopyRow.atomOccurrence d k h _).source e
  target e := by
    by_cases term : i.val < k
    · simp only [dite_eq_left term]
      exact (BoxPullWeakening.CopyRow.termOccurrence d k h _).target e
    · simp only [dite_eq_right term]
      exact (BoxPullWeakening.CopyRow.atomOccurrence d k h _).target e

theorem resource_input (i : Frame.Resource k h) (b : Bool) :
    (resource (d := d) i).ports (.input (if b then ⟨1,by simp⟩ else ⟨0,by simp⟩)) =
      .input (CopyRule.copyOutput k h b i) := by
  by_cases term : i.val < k
  · simp only [resource, dite_eq_left term]
    have idx : EnvironmentPermutation.termIndex (h := h) (⟨i.val,term⟩ : Fin k) = i := Fin.ext rfl
    conv => rhs; rw [← idx]
    rw [BoxPullWeakening.RetainedCopy.copyOutput_eq,PairBoundary.term_index]
    cases b <;> apply congrArg Port.input <;> apply Fin.ext <;>
      simp [
        Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,Distributor.inputIndex,
        FinGrid.index,EnvironmentPermutation.termIndex,PairBoundary.use]
  · simp only [resource, dite_eq_right term]
    have idx : EnvironmentPermutation.atomIndex (k := k) (⟨i.val-k,by
        have bound := i.isLt
        simp only [environmentInterface,List.length_append,List.length_replicate] at bound
        omega⟩ : Fin h) = i := Fin.ext (by dsimp [EnvironmentPermutation.atomIndex];omega)
    conv => rhs; rw [← idx]
    rw [BoxPullWeakening.RetainedCopy.copyOutput_eq,PairBoundary.atom_index]
    cases b <;> apply congrArg Port.input <;> apply Fin.ext <;>
      simp [atomPosition,
        Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,Distributor.inputIndex,
        FinGrid.index,EnvironmentPermutation.atomIndex,PairBoundary.use]

theorem resource_output (i : Frame.Resource k h) :
    (resource (d := d) i).ports (.output 0) = .output i := by
  by_cases term : i.val < k
  · simp only [resource,dite_eq_left term]
    exact congrArg Port.output (Fin.ext rfl)
  · simp only [resource,dite_eq_right term]
    apply congrArg Port.output
    apply Fin.ext
    simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,atomPosition]
    omega

/-- Distinct resource rows retain disjoint original edge carriers. -/
theorem resource_disjoint (i j : Frame.Resource k h) (different : i ≠ j) :
    ∀ e a, (resource (d := d) i).edges e ≠ (resource j).edges a := by
  intro e a eq
  by_cases ti : i.val < k <;> by_cases tj : j.val < k
  · simp only [resource,dite_eq_left ti,dite_eq_left tj] at eq
    have indices := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
    exact different (Fin.ext (congrArg (fun p : Fin k => p.val) indices))
  · simp only [resource,dite_eq_left ti,dite_eq_right tj] at eq
    cases eq
  · simp only [resource,dite_eq_right ti,dite_eq_left tj] at eq
    cases eq
  · simp only [resource,dite_eq_right ti,dite_eq_right tj] at eq
    have indices := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
    have values := congrArg Fin.val indices
    change i.val-k=j.val-k at values
    exact different (Fin.ext (by omega))

/-- The original environment distributor is exhausted by its actual rows. -/
theorem resource_cover (e : (Translation.environmentDistributor d k h 2).Edge) :
    ∃ i : Frame.Resource k h, ∃ a, (resource i).edges a = e := by
  rcases e with ⟨b,e⟩
  cases b <;> rcases e with ⟨i,e⟩
  · refine ⟨EnvironmentPermutation.termIndex i,e,?_⟩
    simp only [resource,EnvironmentPermutation.termIndex,dite_eq_left i.isLt]
    rfl
  · refine ⟨EnvironmentPermutation.atomIndex i,e,?_⟩
    have neg : ¬(EnvironmentPermutation.atomIndex (k := k) i).val < k := by
      simp [EnvironmentPermutation.atomIndex]
    simp only [resource,dite_eq_right neg]
    apply congrArg (Sigma.mk true)
    have eq : atomPosition (EnvironmentPermutation.atomIndex (k := k) i) neg = i :=
      Fin.ext (by simp [atomPosition,EnvironmentPermutation.atomIndex])
    exact congrArg (fun j : Fin h => (⟨j,e⟩ : (Distributor.atDepth .atom h 2 d).Edge)) eq

variable (T : ContractionTree .term (n+2)) (H : Hypernet d [.term] (environmentInterface k h))

noncomputable def innerRow (i : Frame.Resource k h) :
    Occurrence (CanonicalTree.atDepth (Frame.sort k h i) 2 d) (afterSecond T H) :=
  (resource i).comp (innerDistributor T H)
noncomputable def outerRow (i : Frame.Resource k h) :
    Occurrence (CanonicalTree.atDepth (Frame.sort k h i) 2 d) (afterSecond T H) :=
  (resource i).comp (outerDistributor T H)

theorem row_link (i : Frame.Resource k h) :
    (innerRow T H i).ports (.output 0) = (outerRow T H i).ports (.input ⟨1,by simp⟩) := by
  change (retained T H).ports (BoundarySerial.rightInsert _ _ ((resource i).ports (.output 0))) =
    BoundarySerial.rightInsert _ _ ((resource i).ports (.input ⟨1,by simp⟩))
  rw [resource_output,Application.right_serial_output,show (resource (d := d) i).ports (.input ⟨1,by simp⟩) = _ from resource_input i true]
  change BoundarySerial.leftInsert _ _ ((pair H _ true).ports (.output i)) = _
  rw [pair_output,CopyRule.serial_left_output,CopyRule.serial_right_input]

theorem row_disjoint (i : Frame.Resource k h) :
    ∀ e a, (innerRow T H i).edges e ≠ (outerRow T H i).edges a := by
  cases d <;> intro e a eq <;> cases eq

/-- Both nested original distributors form one actual connected six-edge row. -/
noncomputable def row (i : Frame.Resource k h) :
    Occurrence (Frame.row (d := d) i false) (afterSecond T H) :=
  (Row.occurrence (innerRow T H i) (outerRow T H i) (row_link T H i) (row_disjoint T H i)).reboundarySource
    (congrArg (List.replicate 3) (Frame.sort_wire k h i)) (congrArg List.singleton (Frame.sort_wire k h i))


theorem outer_input (i : Frame.Resource k h) :
    (outerRow T H i).ports (.input ⟨0,by simp⟩) = (first T H).ports (.output i) := by
  change BoundarySerial.rightInsert _ _ ((resource i).ports (.input ⟨0,by simp⟩)) =
    BoundarySerial.leftInsert _ _ ((pair H _ false).ports (.output i))
  rw [show (resource (d := d) i).ports (.input ⟨0,by simp⟩) = _ from resource_input i false,
    pair_output,CopyRule.serial_right_input,CopyRule.serial_left_output]

theorem inner_input_active (i : Frame.Resource k h) :
    (innerRow T H i).ports (.input ⟨0,by simp⟩) = (second T H).ports (.output i) := by
  dsimp only [innerRow,innerDistributor,second,Occurrence.comp,Function.comp_apply]
  apply congrArg (retained T H).ports
  change BoundarySerial.rightInsert _ _ ((resource i).ports (.input ⟨0,by simp⟩)) =
    BoundarySerial.leftInsert _ _ (CopyRule.pairInsert (CopyRule.residualTree T) H false (.output i))
  rw [show (resource (d := d) i).ports (.input ⟨0,by simp⟩) = _ from resource_input i false,
    CopyRule.pair_output,CopyRule.serial_right_input,CopyRule.serial_left_output]

theorem inner_input_retained (i : Frame.Resource k h) :
    (innerRow T H i).ports (.input ⟨1,by simp⟩) = (third T H).ports (.output i) := by
  dsimp only [innerRow,innerDistributor,third,remaining,Occurrence.comp,Function.comp_apply]
  apply congrArg (retained T H).ports
  change BoundarySerial.rightInsert _ _ ((resource i).ports (.input ⟨1,by simp⟩)) =
    BoundarySerial.leftInsert _ _ (CopyRule.pairInsert (CopyRule.residualTree T) H true
      (BoundarySerial.rightInsert _ _ (.output i)))
  rw [Application.right_serial_output,
    show (resource (d := d) i).ports (.input ⟨1,by simp⟩) = _ from resource_input i true,
    CopyRule.pair_output,CopyRule.serial_right_input,CopyRule.serial_left_output]

/-- All three row inputs remain attached to the original corresponding
payload output; these are exact coordinates, not just unlabelled paths. -/
theorem row_input (i : Frame.Resource k h) (b : Fin 3) :
    (row T H i).ports (.input ⟨b.val,by simp⟩) =
      (if b.val = 0 then first T H else if b.val = 1 then second T H else third T H).ports (.output i) := by
  rcases Frame.triple b with rfl | rfl | rfl
  · exact outer_input T H i
  · exact inner_input_active T H i
  · exact inner_input_retained T H i

theorem row_output (i : Frame.Resource k h) :
    (row T H i).ports (.output 0) = .output i := by
  change BoundarySerial.rightInsert _ _ ((resource i).ports (.output 0)) = _
  rw [resource_output,Application.right_serial_output]


theorem rows_disjoint (i j : Frame.Resource k h) (different : i ≠ j) :
    ∀ e a, (row T H i).edges e ≠ (row T H j).edges a := by
  cases d
  all_goals
    rintro ⟨b,e⟩ ⟨c,a⟩ eq
    cases b <;> cases c
    · apply resource_disjoint i j different e a
      exact (Occurrence.serialRight _ _).edge_injective ((retained T H).edge_injective eq)
    · cases eq
    · cases eq
    · exact resource_disjoint i j different e a ((Occurrence.serialRight _ _).edge_injective eq)

end Hypernets.Copying.CopyingDouble.Components
