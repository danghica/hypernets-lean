import Hypernets.Copying.ParametricitySmallBareSource
import Hypernets.Copying.ParametricityBareApplyJoin
import Hypernets.Copying.OccurrenceCutBoundary

/-! Complete reconstruction identifies the computed smaller-beta source
with the original application context around its whole Figure20 family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallBareSource
open Graph Opening Combined
variable {m₁ m₂} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))

theorem head_input : (head d T).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  change CompleteMatchCut.replacePort (SmallBareApplication.bodyOccurrence d T).matchEmbedding
    (SmallBareApplication.bodyOccurrence d T).label (localSource d) (.input 0) = _
  exact CompleteMatchCut.replace_input _ _ _ _ (SmallBareApplication.body_input d T)

theorem remaining_input (i : Fin (List.replicate (m₁+m₂) Wire.term).length) :
    (remaining d T).ports (.input i) = .input ⟨i.val+1,by have:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_nil] at *; omega⟩ := by
  apply Occurrence.acrossCut_input
  change (SmallBareApplication.privateOccurrence d T).ports
    (TailPrecompose.leftInsert (leftFamily d m₁ m₂) (PrivateRead.before T (d+2)) (.input i)) = _
  rw [TailPrecompose.left_input]
  rfl

theorem closed_input_succ (i : Fin (m₁+m₂)) :
    (closedFamily d T).ports (.input ⟨i.val+1,by simp⟩) = .input ⟨i.val+1,by simp⟩ := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  have index : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports
      (.input ⟨i.val,by simp⟩) = .input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m₁+m₂) Wire.term).length) :=
    congrArg Port.input (Fin.ext (Nat.add_comm _ _))
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T) (remaining d T) (selected_remaining_disjoint d T)).ports (.input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m₁+m₂) Wire.term).length)) = _
  rw [← index,Occurrence.tensorJoin_right,remaining_input]

theorem argument_output : (head d T).ports (.output (1 : Fin 2)) = .output ⟨0,by decide⟩ := by
  change CompleteMatchCut.replacePort (SmallBareApplication.bodyOccurrence d T).matchEmbedding
    (SmallBareApplication.bodyOccurrence d T).label (localSource d) (.output 0) = _
  exact CompleteMatchCut.replace_output _ _ _ _ (SmallBareApplication.body_bound d T)

/-- The original bare application contains the complete original family and
private cell, while its argument remains a boundary wire. -/
noncomputable def sourceOccurrence : Occurrence
    ((BareApplyFirst.net (closedGraph d T)).reboundary (List.append_nil _).symm rfl) (host d T) :=
  (BareApplyFirst.Join.occurrence (closedGraph d T) (head d T) (closedFamily d T)
    (head_function d T) (head_family_disjoint d T)).reboundarySource _ _

theorem input (i : Fin (List.replicate ((m₁+m₂)+1) Wire.term ++ []).length) :
    (sourceOccurrence d T).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    rw [eq]
    change (BareApplyFirst.Join.occurrence (closedGraph d T) (head d T) (closedFamily d T) (head_function d T) (head_family_disjoint d T)).ports (.input ⟨0,by simp⟩) = _
    rw [BareApplyFirst.Join.input_zero,head_input]
  · let j : Fin (m₁+m₂) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_append,List.length_replicate,List.length_nil] at h; omega⟩
    have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
    rw [eq]
    change (BareApplyFirst.Join.occurrence (closedGraph d T) (head d T) (closedFamily d T) (head_function d T) (head_family_disjoint d T)).ports (.input ⟨j.val+1,by simp⟩) = _
    rw [BareApplyFirst.Join.input_succ,closed_input_succ]

theorem output (i : Fin ([Wire.term].length)) : (sourceOccurrence d T).ports (.output i) = .output i := by
  change Fin 1 at i
  have zero : i=0 := Subsingleton.elim _ _
  subst i
  change (BareApplyFirst.Join.occurrence (closedGraph d T) (head d T) (closedFamily d T)
    (head_function d T) (head_family_disjoint d T)).ports (.output 0) = _
  rw [BareApplyFirst.Join.output,argument_output]
  rfl

theorem covers_head (e : (primitiveNet (d+2) (.operation .app)).Edge) :
    ∃ a, (sourceOccurrence d T).edges a = (head d T).edges e := ⟨⟨false,e⟩,rfl⟩
theorem covers_selected (e : (smallLeft (d+1)).Edge) :
    ∃ a, (sourceOccurrence d T).edges a = (selected d T).edges e :=
  ⟨⟨true,⟨false,⟨false,e⟩⟩⟩,rfl⟩
theorem covers_remaining (e : (leftFamily d m₁ m₂).Edge) :
    ∃ a, (sourceOccurrence d T).edges a = (remaining d T).edges e :=
  ⟨⟨true,⟨false,⟨true,e⟩⟩⟩,rfl⟩
theorem covers_cell (e : (Serial.net (T.atDepth (d+2)) (privateCell (d+2))).Edge) :
    ∃ a, (sourceOccurrence d T).edges a = (cell d T).edges e :=
  ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Before the inverse beta cut, only the actual reader and discarded
argument belong to the removed component; all other edges belong to the
unchanged remaining family or the complete original private cell. -/
theorem opened_cover (e : (SmallBareApplication.opened d T).Edge) :
    (∃ a, (SmallBareApplication.bodyOccurrence d T).edges a = e) ∨
    (∃ a, (oldFamily d T).edges a = e) ∨
    ∃ a, (oldCell d T).edges a = e := by
  rcases e with ⟨part,e⟩
  cases part
  · rcases e with ⟨part,e⟩
    cases part
    · exact .inr (.inl ⟨e,rfl⟩)
    · rcases PrivateSource.cover T (d+2) e with eq | ⟨a,eq⟩
      · subst e
        left
        refine ⟨(SmallBareApplication.bodyIso d).edges.invFun ⟨false,(0 : Fin 1)⟩,?_⟩
        exact congrArg (fun e : (readBody (d+2)).Edge =>
          (BoxPullWeakening.AdjoinOccurrence.components _ .term (SmallBareApplication.reader d T)
            (SmallBareApplication.weakeningOccurrence d T) e.1).edges e.2)
          ((SmallBareApplication.bodyIso d).edges.right_inv ⟨false,(0 : Fin 1)⟩)
      · right; right
        refine ⟨a,?_⟩
        change (SmallBareApplication.privateOccurrence d T).edges
          ((TailPrecompose.rightOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))).edges
            ((PrivateSource.occurrence T (d+2)).edges a)) = _
        rw [eq]
        rfl
  · left
    refine ⟨(SmallBareApplication.bodyIso d).edges.invFun ⟨true,e⟩,?_⟩
    exact congrArg (fun e : (readBody (d+2)).Edge =>
      (BoxPullWeakening.AdjoinOccurrence.components _ .term (SmallBareApplication.reader d T)
        (SmallBareApplication.weakeningOccurrence d T) e.1).edges e.2)
      ((SmallBareApplication.bodyIso d).edges.right_inv ⟨true,e⟩)

/-- Every actual source edge is covered by the three original components;
this includes all unused sharing siblings and every argument resource edge. -/
theorem cover : Function.Surjective (sourceOccurrence d T).edges := by
  rintro (⟨e,ne⟩ | e)
  · cases e with
    | none => exact False.elim (ne rfl)
    | some retained =>
      obtain ⟨e,avoid⟩ := retained
      rcases opened_cover d T e with ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩
      · exact False.elim (avoid a eq)
      · obtain ⟨x,h⟩ := covers_remaining d T a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
      · obtain ⟨x,h⟩ := covers_cell d T a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
  · cases e
    · exact covers_head d T (0 : Fin 1)
    · exact covers_selected d T ⟨false,(0 : Fin 1)⟩
    · exact covers_selected d T ⟨true,(0 : Fin 1)⟩

/-- The complete source is the original application context around the
entire original Figure20 family, with only equal-interface presentation casts.
The map fixes every external input and argument output. -/
noncomputable def iso : DeepIso
    ((BareApplyFirst.net (closedGraph d T)).reboundary (List.append_nil _).symm rfl)
    (SmallBareApplication.before d T) :=
  (sourceOccurrence d T).iso_of_edge_surjective (input d T) (output d T) (cover d T)

end Hypernets.Copying.Parametricity.SmallBareSource
