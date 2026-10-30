import Hypernets.Copying.BoxPullContractionRowOccurrence
import Hypernets.Copying.OccurrenceAcrossCut

/-! The original payload copies and residual contraction tree survive the
literal four-input sharing interchange. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

/-- The complete payload is preserved by attaching its output contraction. -/
def payload : Occurrence H (merged s H) := by
  cases d
  all_goals
    refine {
      ports := fun v => Port.cast rfl (one_interface s k h)
        (oldPort s (H.reboundary rfl (two_interface s k h)) (Port.cast rfl (two_interface s k h) v))
      internals := fun v => .inr ⟨false,v⟩
      edges := fun e => ⟨false,e⟩
      internal_map := fun _ => rfl
      internal_injective := ?_
      edge_injective := ?_
      internal_label := fun _ => rfl
      label := fun _ => labelEquiv_refl _ _
      source := ?_
      target := ?_ }
    · intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
    · intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
    · intro e
      change (H.source e).map _ = (((H.source e).map _).map _).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      exact congrArg (Port.cast rfl (one_interface s k h))
        (oldPort_insert s (H.reboundary rfl (two_interface s k h))
          (Port.cast rfl (two_interface s k h) v)).symm
    · intro e
      change (H.target e).map _ = (((H.target e).map _).map _).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      exact congrArg (Port.cast rfl (one_interface s k h))
        (oldPort_insert s (H.reboundary rfl (two_interface s k h))
          (Port.cast rfl (two_interface s k h) v)).symm

theorem payload_input (i : Fin 1) : (payload s H).ports (.input i) = .input i := by cases d <;> rfl

/-- The residual tree and retained payload form their original complete branch. -/
noncomputable def retainedBranch :
    Occurrence (Serial.net (CopyRule.residual T d) H)
      (Serial.net (CopyRule.residual T d) (merged s H)) := by
  apply Occurrence.SerialJoin.occurrence
    (BoxPullWeakening.RetainedCopy.serialLeftOccurrence (CopyRule.residual T d) (merged s H))
    ((payload s H).comp (Occurrence.serialRight _ _))
  · intro i
    change BoundarySerial.leftInsert _ _ (.output i) =
      BoundarySerial.rightInsert _ _ ((payload s H).ports (.input i))
    rw [payload_input,CopyRule.serial_left_output,CopyRule.serial_right_input]
  · cases d <;> intro a b eq <;> cases eq

theorem retainedBranch_output (i : Fin (environmentInterface (variables s k 2) (atoms s h 2)).length) :
    (retainedBranch T s H).ports (.output i) =
      BoundarySerial.rightInsert (CopyRule.residual T d) (merged s H) ((payload s H).ports (.output i)) := by
  unfold retainedBranch
  rw [Occurrence.SerialJoin.occurrence_output]
  rfl

noncomputable def payloadComponents (b : Bool) :
    Occurrence (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H) b)
      (CopyRule.copies T (merged s H)) :=
  match b with
  | false => (payload s H).comp (BoxPullWeakening.RetainedCopy.copyComponent T (merged s H) false)
  | true => (retainedBranch T s H).comp
      (BoxPullWeakening.RetainedCopy.copyComponent T (merged s H) true)

theorem payloadComponents_disjoint : ∀ a b, a ≠ b → ∀ e c,
    (payloadComponents T s H a).edges e ≠ (payloadComponents T s H b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · cases eq
  · cases eq
  · exact ne rfl

/-- Both copies and the complete residual tree occur jointly in the original
reduct, before any sharing-row replacement. -/
noncomputable def copies : Occurrence (CopyRule.copies T H) (CopyRule.copies T (merged s H)) :=
  (Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H))
    (CopyRule.pairBoundary n (variables s k 2) (atoms s h 2))
    ⟨[false,true],by intro b; cases b <;> simp⟩ (payloadComponents T s H)
    (payloadComponents_disjoint T s H)).reboundarySource
      (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

noncomputable def originalCopies : Occurrence (CopyRule.copies T H) (CopyRule.after T (merged s H)) :=
  (copies T s H).comp (BoxPullWeakening.RetainedCopy.serialLeftOccurrence _ _)

theorem originalCopies_disjoint : ∀ a b,
    (insideOccurrence T s H).edges a ≠ (originalCopies T s H).edges b := by
  cases d
  all_goals
    rintro ⟨a,e⟩ ⟨b,c⟩ eq
    cases a <;> cases b
    · rcases e with ⟨u,e⟩; cases u <;> cases eq
    · rcases e with ⟨u,e⟩; cases u
      all_goals rcases c with ⟨v,c⟩; cases v <;> cases eq
    · cases eq
    · cases eq

/-- The original pair of payloads survives the computed row replacement,
including every deep box and every unused residual-tree branch. -/
noncomputable def correctedCopies : Occurrence (CopyRule.copies T H) (corrected T s H) :=
  (insideOccurrence T s H).acrossCut (originalCopies T s H) (originalCopies_disjoint T s H)
    (outside d s)

/-- The full seven-edge replacement row has its literal occurrence. -/
noncomputable def inserted : Occurrence (outside d s) (corrected T s H) := by
  unfold corrected CompleteMatchCut.replaceWith
  exact (BoxPullWeakening.RetainedCopy.targetCast (Occurrence.ofIso (DeepIso.refl (outside d s)))
    (CompleteMatchCut.hole_input (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm
    (CompleteMatchCut.hole_output (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label).symm).comp
      (Occurrence.plug (CompleteMatchCut.net (insideOccurrence T s H).matchEmbedding (insideOccurrence T s H).label) none _)

/-- The new contraction is attached to the two original selected outputs. -/
def resource (j : Fin 2) : Fin (environmentInterface (variables s k 2) (atoms s h 2)).length :=
  ⟨k+j.val,by clear T H; cases s <;> simp [variables,atoms,environmentInterface] <;> have := j.isLt <;> omega⟩

theorem outer_input (j : Fin 2) : (outer s H).ports (.input j) = .internal (.inl j) := by
  have casesJ : j = 0 ∨ j = 1 := by
    by_cases z : j.val = 0
    · exact .inl (Fin.ext z)
    · exact .inr (Fin.ext (by have := j.isLt; omega))
  cases d <;> rcases casesJ with rfl | rfl <;> rfl

theorem payload_selected (j : Fin 2) :
    (payload s H).ports (.output (resource (k := k) (h := h) s j)) = (outer s H).ports (.input j) := by
  rw [outer_input]
  cases d
  all_goals
    change Port.cast rfl (one_interface s k h)
      (oldPort s (H.reboundary rfl (two_interface s k h))
        (Port.cast rfl (two_interface s k h) (.output (resource s j)))) = _
    have before : ¬ k+j.val < (List.replicate k Wire.term).length := by simp
    have middle : k+j.val < (List.replicate k Wire.term).length+2 := by simp
    simp only [Port.cast,resource,oldPort,Fin.val_cast,before,middle,↓reduceIte]
    apply congrArg Port.internal
    apply congrArg Sum.inl
    apply Fin.ext
    simp

theorem copies_component (b : Bool)
    (v : (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H) b).Vertex) :
    (copies T s H).ports (CopyRule.pairInsert T H b v) = (payloadComponents T s H b).ports v := by
  unfold copies CopyRule.pairInsert
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]

/-- Ordered source positions of the four-input inside row are exactly the
selected outputs of the two original payload copies. -/
theorem inside_input_link (b : Bool) (j : Fin 2) :
    (originalCopies T s H).ports
      (.output (CopyRule.copyOutput (variables s k 2) (atoms s h 2) b (resource s j))) =
    (insideOccurrence T s H).ports (.input ⟨(if b then 2 else 0)+j.val,by cases b <;> simp <;> have := j.isLt <;> omega⟩) := by
  have casesJ : j = 0 ∨ j = 1 := by
    by_cases z : j.val = 0
    · exact .inl (Fin.ext z)
    · exact .inr (Fin.ext (by have := j.isLt; omega))
  cases b
  all_goals
    change BoundarySerial.leftInsert _ _ ((copies T s H).ports _) = _
    first
    | (have law := copies_component T s H false (.output (resource s j))
       rw [CopyRule.pair_output] at law
       rw [law])
    | (have law := copies_component T s H true (.output (resource s j))
       rw [CopyRule.pair_output] at law
       rw [law])
    rcases casesJ with rfl | rfl
  all_goals
    rw [insideOccurrence,Occurrence.SerialJoin.occurrence_input]
    first
    | (change BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) false
        ((payload s H).ports (.output (resource s _)))) =
        BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) false
          ((outer s H).ports (.input _)))
       rw [payload_selected])
    | (change BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) true
        ((retainedBranch T s H).ports (.output (resource s _)))) =
        BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) true
          (BoundarySerial.rightInsert _ _ ((outer s H).ports (.input _))))
       rw [retainedBranch_output,payload_selected])

  all_goals simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.split,primitiveSignature]
  all_goals rfl

/-- Every unselected output keeps its literal order after merging the pair. -/
def collapsedOutput (i : Fin (environmentInterface (variables s k 2) (atoms s h 2)).length) :
    Fin (environmentInterface (variables s k 1) (atoms s h 1)).length :=
  ⟨if i.val < k then i.val else i.val-1,by
    clear T H
    have bound := i.isLt
    cases s <;> simp [variables,atoms,environmentInterface] at * <;> split <;> omega⟩

theorem payload_unselected (i : Fin (environmentInterface (variables s k 2) (atoms s h 2)).length)
    (away : i.val < k ∨ k+2 ≤ i.val) :
    (payload s H).ports (.output i) = .output (collapsedOutput s i) := by
  cases d
  all_goals
    change Port.cast rfl (one_interface s k h)
      (oldPort s (H.reboundary rfl (two_interface s k h)) (Port.cast rfl (two_interface s k h) (.output i))) = _
    rcases away with before | after
    · simp [oldPort,Port.cast,collapsedOutput,before]
    · have before : ¬ i.val < k := by omega
      have middle : ¬ i.val < k+2 := by omega
      simp [oldPort,Port.cast,collapsedOutput,before,middle]

theorem originalCopies_unselected (b : Bool)
    (i : Fin (environmentInterface (variables s k 2) (atoms s h 2)).length)
    (away : i.val < k ∨ k+2 ≤ i.val) :
    (originalCopies T s H).ports (.output (CopyRule.copyOutput (variables s k 2) (atoms s h 2) b i)) =
      .internal (.inl (CopyRule.copyOutput (variables s k 1) (atoms s h 1) b (collapsedOutput s i))) := by
  cases b
  · have law := copies_component T s H false (.output i)
    rw [CopyRule.pair_output] at law
    change BoundarySerial.leftInsert _ _ ((copies T s H).ports _) = _
    rw [law]
    change BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) false ((payload s H).ports (.output i))) = _
    rw [payload_unselected s H i away,CopyRule.pair_output,CopyRule.serial_left_output]
  · have law := copies_component T s H true (.output i)
    rw [CopyRule.pair_output] at law
    change BoundarySerial.leftInsert _ _ ((copies T s H).ports _) = _
    rw [law]
    change BoundarySerial.leftInsert _ _ (CopyRule.pairInsert T (merged s H) true ((retainedBranch T s H).ports (.output i))) = _
    rw [retainedBranch_output,payload_unselected s H i away,Application.right_serial_output,
      CopyRule.pair_output,CopyRule.serial_left_output]

end Hypernets.Copying.BoxPullContraction.CopyRows
