import Hypernets.Copying.ParametricityLargeBareSource
import Hypernets.Copying.ParametricityBareApplyJoin
import Hypernets.Copying.OccurrenceCutBoundary
import Hypernets.Copying.ParametricityTensorCut

/-! Complete reconstruction identifies the computed larger-beta source
with the original application context around its whole Figure20 family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeBareSource
open Graph Opening Combined
variable {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1))

theorem head_input : (head d C).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  change CompleteMatchCut.replacePort (LargeBareApplication.leftBody d C).matchEmbedding
    (LargeBareApplication.leftBody d C).label (localSource d) (.input 0) = _
  exact CompleteMatchCut.replace_input _ _ _ _ (LargeBareApplication.left_input d C)

theorem remaining_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (remaining d C).ports (.input i) = .input ⟨i.val+1,by have:=i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  apply Occurrence.acrossCut_input
  have bound : i.val < m+n := by simpa using i.isLt
  change (privateFamily d C).ports
    ((BoxPullWeakening.ReverseComponents.serialLeft
      (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))).ports
        ((BoxPullWeakening.ReverseComponents.serialLeft
          (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))).ports (.input ⟨1+i.val,by simp;omega⟩))) = _
  change (privateFamily d C).ports
    (BoundarySerial.leftInsert _ _ (BoundarySerial.leftInsert _ _ (.input _))) = _
  rw [left_input,left_input]
  have index : (⟨1+i.val,by simp;omega⟩ : Fin (List.replicate ((m+n)+1) Wire.term).length) =
      ⟨i.val+1,by simp;have:=i.isLt;simp only [List.length_replicate] at this;omega⟩ := Fin.ext (Nat.add_comm _ _)
  rw [index]
  change (BoxPullWeakening.ReverseComponents.serialLeft
    (BareApplyFirst.net (IsolatedFamily.smallClosed d C)) (callback (d+2))).ports
      ((BareApplyFirst.family (IsolatedFamily.smallClosed d C)).ports (.input ⟨i.val+1,by simp;omega⟩)) = _
  have boundary : (BoxPullWeakening.ReverseComponents.serialLeft
    (BareApplyFirst.net (IsolatedFamily.smallClosed d C)) (callback (d+2))).ports
      (.input ⟨i.val+1,by simp;omega⟩) = .input ⟨i.val+1,by simp;omega⟩ := by
    simpa only [BoxPullWeakening.ReverseComponents.serialLeft,MatchEmbedding.occurrence,
      MatchEmbedding.serialLeft] using
      (left_input (BareApplyFirst.net (IsolatedFamily.smallClosed d C)) (callback (d+2)) ⟨i.val+1,by simp;omega⟩)
  exact (congrArg (BoxPullWeakening.ReverseComponents.serialLeft
    (BareApplyFirst.net (IsolatedFamily.smallClosed d C)) (callback (d+2))).ports
      (BareApplyFirst.family_succ (IsolatedFamily.smallClosed d C) ⟨i.val,bound⟩)).trans
        boundary

theorem closed_input_succ (i : Fin (m+n)) :
    (closedFamily d C).ports (.input ⟨i.val+1,by simp⟩) = .input ⟨i.val+1,by simp⟩ := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  have index : (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (leftFamily d m n)).ports
      (.input ⟨i.val,by simp⟩) = .input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m+n) Wire.term).length) :=
    congrArg Port.input (Fin.ext (Nat.add_comm _ _))
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C) (remaining d C) (selected_remaining_disjoint d C)).ports (.input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m+n) Wire.term).length)) = _
  rw [← index,Occurrence.tensorJoin_right,remaining_input]

theorem argument_output : (head d C).ports (.output (1 : Fin 2)) = .output ⟨0,by decide⟩ := by
  change CompleteMatchCut.replacePort (LargeBareApplication.leftBody d C).matchEmbedding
    (LargeBareApplication.leftBody d C).label (localSource d) (.output 0) = _
  exact CompleteMatchCut.replace_output _ _ _ _ (LargeBareApplication.left_argument d C)

/-- The original bare application contains the complete original family and
private cell, while its argument remains a boundary wire. -/
noncomputable def sourceOccurrence : Occurrence
    (BareApplyFirst.net (closedGraph d C)) (host d C) :=
  (BareApplyFirst.Join.occurrence (closedGraph d C) (head d C) (closedFamily d C)
    (head_function d C) (head_family_disjoint d C))

theorem input (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (sourceOccurrence d C).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    rw [eq]
    change (BareApplyFirst.Join.occurrence (closedGraph d C) (head d C) (closedFamily d C) (head_function d C) (head_family_disjoint d C)).ports (.input ⟨0,by simp⟩) = _
    rw [BareApplyFirst.Join.input_zero,head_input]
  · let j : Fin (m+n) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
    have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
    rw [eq]
    change (BareApplyFirst.Join.occurrence (closedGraph d C) (head d C) (closedFamily d C) (head_function d C) (head_family_disjoint d C)).ports (.input ⟨j.val+1,by simp⟩) = _
    rw [BareApplyFirst.Join.input_succ,closed_input_succ]

theorem output (i : Fin ([Wire.term].length)) : (sourceOccurrence d C).ports (.output i) = .output i := by
  change Fin 1 at i
  have zero : i=0 := Subsingleton.elim _ _
  subst i
  change (BareApplyFirst.Join.occurrence (closedGraph d C) (head d C) (closedFamily d C)
    (head_function d C) (head_family_disjoint d C)).ports (.output 0) = _
  rw [BareApplyFirst.Join.output,argument_output]
  rfl

theorem covers_head (e : (primitiveNet (d+2) (.operation .app)).Edge) :
    ∃ a, (sourceOccurrence d C).edges a = (head d C).edges e := ⟨⟨false,e⟩,rfl⟩
theorem covers_selected (e : (largeLeft d).Edge) :
    ∃ a, (sourceOccurrence d C).edges a = (selected d C).edges e :=
  ⟨⟨true,⟨false,⟨false,e⟩⟩⟩,rfl⟩
theorem covers_remaining (e : (leftFamily d m n).Edge) :
    ∃ a, (sourceOccurrence d C).edges a = (remaining d C).edges e :=
  ⟨⟨true,⟨false,⟨true,e⟩⟩⟩,rfl⟩
theorem covers_cell (e : (Serial.net (C.atDepth (d+2)) (privateCell (d+2))).Edge) :
    ∃ a, (sourceOccurrence d C).edges a = (cell d C).edges e :=
  ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Before the inverse beta cut, only the actual reader and discarded
argument belong to the removed component; all other edges belong to the
unchanged remaining family or the complete original private cell. -/
theorem covers_raw_body (e : (LargeSplice.raw (hasPrivate := true) (smallLeft (d+1)) (callback (d+2))).Edge) :
    ∃ a, (LargeBareApplication.leftBody d C).edges a =
      (BareCall.rawOccurrence (hasPrivate := true) (IsolatedFamily.smallClosed d C)
        (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C)
        (LargeFamilyApplication.left_member_input d C)).edges e := by
  refine ⟨(LargeOpening.read_bodyIso (d := d)).edges.invFun e, ?_⟩
  exact congrArg (BareCall.rawOccurrence (hasPrivate := true) (IsolatedFamily.smallClosed d C)
    (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C)
    (LargeFamilyApplication.left_member_input d C)).edges
      ((LargeOpening.read_bodyIso (d := d)).edges.right_inv e)

theorem opened_cover (e : (LargeBareApplication.leftAfter d C).Edge) :
    (∃ a, (LargeBareApplication.leftBody d C).edges a = e) ∨
    (∃ a, (oldFamily d C).edges a = e) ∨
    ∃ a, (oldCell d C).edges a = e := by
  rcases e with ⟨part,e⟩
  cases part
  · rcases e with ⟨part,e⟩
    cases part
    · exact .inl (covers_raw_body d C ⟨false,e⟩)
    · rcases e with ⟨part,e⟩
      cases part
      · rcases e with ⟨part,e⟩
        cases part
        · rcases e with ⟨part,e⟩
          cases part
          · exact .inl (covers_raw_body d C ⟨true,⟨false,e⟩⟩)
          · exact .inr (.inl ⟨e,rfl⟩)
        · exact .inr (.inr ⟨⟨false,e⟩,rfl⟩)
      · exact .inr (.inr ⟨⟨true,e⟩,rfl⟩)
  · exact .inl (covers_raw_body d C ⟨true,⟨true,e⟩⟩)

/-- Every actual source edge is covered by the three original components;
this includes all unused sharing siblings and every argument resource edge. -/
theorem cover : Function.Surjective (sourceOccurrence d C).edges := by
  rintro (⟨e,ne⟩ | e)
  · cases e with
    | none => exact False.elim (ne rfl)
    | some retained =>
      obtain ⟨e,avoid⟩ := retained
      rcases opened_cover d C e with ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩
      · exact False.elim (avoid a eq)
      · obtain ⟨x,h⟩ := covers_remaining d C a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
      · obtain ⟨x,h⟩ := covers_cell d C a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
  · cases e
    · exact covers_head d C (0 : Fin 1)
    · exact covers_selected d C ⟨false,(0 : Fin 1)⟩
    · exact covers_selected d C ⟨true,(0 : Fin 1)⟩

/-- The complete source is the original application context around the
entire original Figure20 family, with only equal-interface presentation casts.
The map fixes every external input and argument output. -/
noncomputable def iso : DeepIso
    (BareApplyFirst.net (closedGraph d C))
    (LargeBareApplication.leftBefore d C) :=
  (sourceOccurrence d C).iso_of_edge_surjective (input d C) (output d C) (cover d C)

end Hypernets.Copying.Parametricity.LargeBareSource
