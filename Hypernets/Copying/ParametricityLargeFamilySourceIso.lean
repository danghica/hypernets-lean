import Hypernets.Copying.ParametricityLargeFamilySource
import Hypernets.Copying.ParametricityApplyJoin
import Hypernets.Copying.OccurrenceCutBoundary
import Hypernets.Copying.ParametricityTensorCut

/-! Complete reconstruction identifies the computed larger-beta source
with the original application context around its whole Figure20 family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeFamilySource
open Graph Opening Combined
variable {m n O} (d : Nat) (C : ContractionTree .term ((m+n)+1))
    (V : Hypernet (d+2) [.term] O)

theorem head_input : (head d C V).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  change CompleteMatchCut.replacePort (LargeFamilyApplication.leftOpened d C V).matchEmbedding
    (LargeFamilyApplication.leftOpened d C V).label (localSource d V) (.input 0) = _
  exact CompleteMatchCut.replace_input _ _ _ _ (LargeFamilyApplication.left_opened_input d C V)

theorem remaining_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (remaining d C V).ports (.input i) = .input ⟨i.val+1,by have:=i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  apply Occurrence.acrossCut_input
  have bound : i.val < m+n := by simpa using i.isLt
  change (privateFamily d C V).ports
    ((BoxPullWeakening.ReverseComponents.serialLeft
      (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))).ports
        ((BoxPullWeakening.ReverseComponents.serialLeft
          (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))).ports (.input ⟨1+i.val,by simp;omega⟩))) = _
  change (privateFamily d C V).ports
    (BoundarySerial.leftInsert _ _ (BoundarySerial.leftInsert _ _ (.input _))) = _
  rw [left_input,left_input]
  have index : (⟨1+i.val,by simp;omega⟩ : Fin (List.replicate ((m+n)+1) Wire.term).length) =
      ⟨i.val+1,by simp;have:=i.isLt;simp only [List.length_replicate] at this;omega⟩ := Fin.ext (Nat.add_comm _ _)
  rw [index]
  exact ApplyFirst.family_succ _ _ ⟨i.val,by have:=i.isLt;simp only [List.length_replicate] at this;exact this⟩

theorem closed_input_succ (i : Fin (m+n)) :
    (closedFamily d C V).ports (.input ⟨i.val+1,by simp⟩) = .input ⟨i.val+1,by simp⟩ := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  have index : (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (leftFamily d m n)).ports
      (.input ⟨i.val,by simp⟩) = .input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m+n) Wire.term).length) :=
    congrArg Port.input (Fin.ext (Nat.add_comm _ _))
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C V) (remaining d C V) (selected_remaining_disjoint d C V)).ports (.input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m+n) Wire.term).length)) = _
  rw [← index,Occurrence.tensorJoin_right,remaining_input]

theorem argument_output (i : Fin O.length) : (argument d C V).ports (.output i) = .output i := by
  let j : Fin ([Wire.term]++O).length := ⟨1+i.val,by simp; omega⟩
  have original : (argument d C V).ports (.output i) = (inserted d C V).ports (.output j) := by
    apply congrArg (inserted d C V).ports
    change BoundarySerial.rightInsert (primitiveNet (d+2) (.operation .app))
      (Net.Tensor.net (largeLeft d) V) (.output j) = .output j
    exact Application.right_serial_output _ _ _
  rw [original]
  apply CompleteMatchCut.replace_output
  change (LargeFamilyApplication.leftOpened d C V).ports (.output j) = _
  unfold LargeFamilyApplication.leftOpened
  rw [ApplyFirst.binaryOccurrence,Occurrence.SerialJoin.occurrence_output]
  have index : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1))
      (LargeOpening.invocation V)).ports (.output i) = .output j := rfl
  change (BoxPullWeakening.ReverseComponents.tensorJoin _ _ _).ports (.output j) = _
  rw [← index,Occurrence.tensorJoin_right]
  exact ApplyFirst.argument_output _ _ i

/-- The generic original application context is realized by its actual head,
whole original private family, and unchanged arbitrary stable argument. -/
noncomputable def sourceOccurrence : Occurrence
    (ApplyFirst.net (closedGraph d C) V) (host d C V) :=
  (ApplyFirst.Join.occurrence (closedGraph d C) V (head d C V) (closedFamily d C V) (argument d C V)
    (head_function d C V) (head_argument d C V) (head_family_disjoint d C V)
    (head_argument_disjoint d C V) (family_argument_disjoint d C V))

theorem input (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (sourceOccurrence d C V).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    rw [eq]
    change (ApplyFirst.Join.occurrence (closedGraph d C) V (head d C V) (closedFamily d C V) (argument d C V) (head_function d C V) (head_argument d C V) (head_family_disjoint d C V) (head_argument_disjoint d C V) (family_argument_disjoint d C V)).ports (.input ⟨0,by simp⟩) = _
    rw [ApplyFirst.Join.input_zero,head_input]
  · let j : Fin (m+n) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
    have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
    rw [eq]
    change (ApplyFirst.Join.occurrence (closedGraph d C) V (head d C V) (closedFamily d C V) (argument d C V) (head_function d C V) (head_argument d C V) (head_family_disjoint d C V) (head_argument_disjoint d C V) (family_argument_disjoint d C V)).ports (.input ⟨j.val+1,by simp⟩) = _
    rw [ApplyFirst.Join.input_succ,closed_input_succ]

theorem output (i : Fin O.length) : (sourceOccurrence d C V).ports (.output i) = .output i := by
  change (ApplyFirst.Join.occurrence (closedGraph d C) V (head d C V) (closedFamily d C V) (argument d C V) (head_function d C V) (head_argument d C V) (head_family_disjoint d C V) (head_argument_disjoint d C V) (family_argument_disjoint d C V)).ports (.output i) = _
  rw [ApplyFirst.Join.output,argument_output]


theorem covers_head (e : (primitiveNet (d+2) (.operation .app)).Edge) :
    ∃ a, (sourceOccurrence d C V).edges a = (head d C V).edges e := ⟨⟨none,e⟩,rfl⟩
theorem covers_argument (e : V.Edge) :
    ∃ a, (sourceOccurrence d C V).edges a = (argument d C V).edges e := ⟨⟨some true,e⟩,rfl⟩
theorem covers_selected (e : (largeLeft d).Edge) :
    ∃ a, (sourceOccurrence d C V).edges a = (selected d C V).edges e :=
  ⟨⟨some false,⟨false,⟨false,e⟩⟩⟩,rfl⟩
theorem covers_remaining (e : (leftFamily d m n).Edge) :
    ∃ a, (sourceOccurrence d C V).edges a = (remaining d C V).edges e :=
  ⟨⟨some false,⟨false,⟨true,e⟩⟩⟩,rfl⟩
theorem covers_cell (e : (Serial.net (C.atDepth (d+2)) (privateCell (d+2))).Edge) :
    ∃ a, (sourceOccurrence d C V).edges a = (cell d C V).edges e :=
  ⟨⟨some false,⟨true,e⟩⟩,rfl⟩

/-- Before the inverse beta cut, the removed component consists of the
application, selected smaller abstraction and complete unevaluated callback
invocation. Every other edge belongs to the unchanged remaining family or
the original private tree and allocated cell. -/
theorem opened_cover (e : (LargeFamilyApplication.leftAfter d C V).Edge) :
    (∃ a, (LargeFamilyApplication.leftOpened d C V).edges a = e) ∨
    (∃ a, (oldFamily d C V).edges a = e) ∨
    ∃ a, (oldCell d C V).edges a = e := by
  rcases e with ⟨part,e⟩
  cases part with
  | none => exact .inl ⟨⟨false,e⟩,rfl⟩
  | some part =>
    cases part
    · rcases e with ⟨part,e⟩
      cases part
      · rcases e with ⟨part,e⟩
        cases part
        · rcases e with ⟨part,e⟩
          cases part
          · exact .inl ⟨⟨true,⟨false,e⟩⟩,rfl⟩
          · exact .inr (.inl ⟨e,rfl⟩)
        · exact .inr (.inr ⟨⟨false,e⟩,rfl⟩)
      · exact .inr (.inr ⟨⟨true,e⟩,rfl⟩)
    · exact .inl ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Every actual source edge is covered by the three original components;
this includes all unused sharing siblings and every argument resource edge. -/
theorem cover : Function.Surjective (sourceOccurrence d C V).edges := by
  rintro (⟨e,ne⟩ | e)
  · cases e with
    | none => exact False.elim (ne rfl)
    | some retained =>
      obtain ⟨e,avoid⟩ := retained
      rcases opened_cover d C V e with ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩
      · exact False.elim (avoid a eq)
      · obtain ⟨x,h⟩ := covers_remaining d C V a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
      · obtain ⟨x,h⟩ := covers_cell d C V a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
  · rcases e with ⟨part,e⟩
    cases part
    · exact covers_head d C V e
    · rcases e with ⟨part,e⟩
      cases part
      · exact covers_selected d C V e
      · exact covers_argument d C V e

/-- The complete source is the original application context around the
entire original Figure20 family, with only equal-interface presentation casts.
The map fixes every external input and argument output. -/
noncomputable def iso : DeepIso
    (ApplyFirst.net (closedGraph d C) V)
    (LargeFamilyApplication.leftBefore d C V) :=
  (sourceOccurrence d C V).iso_of_edge_surjective (input d C V) (output d C V) (cover d C V)

end Hypernets.Copying.Parametricity.LargeFamilySource
