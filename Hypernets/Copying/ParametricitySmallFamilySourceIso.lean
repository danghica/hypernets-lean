import Hypernets.Copying.ParametricitySmallFamilySource
import Hypernets.Copying.ParametricityApplyJoin
import Hypernets.Copying.OccurrenceCutBoundary

/-! Complete reconstruction identifies the computed smaller-beta source
with the original application context around its whole Figure20 family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallFamilySource
open Graph Opening Combined
variable {m₁ m₂ O} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))
    (V : Hypernet (d+2) [.term] O)

theorem head_input : (head d T V).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  change CompleteMatchCut.replacePort (SmallFamilyApplication.bodyOccurrence d T V).matchEmbedding
    (SmallFamilyApplication.bodyOccurrence d T V).label (localSource d V) (.input 0) = _
  exact CompleteMatchCut.replace_input _ _ _ _ (SmallFamilyApplication.body_input d T V)

theorem remaining_input (i : Fin (List.replicate (m₁+m₂) Wire.term).length) :
    (remaining d T V).ports (.input i) = .input ⟨i.val+1,by have:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_nil] at *; omega⟩ := by
  apply Occurrence.acrossCut_input
  change (SmallFamilyApplication.privateOccurrence d T V).ports
    (TailPrecompose.leftInsert (leftFamily d m₁ m₂) (PrivateRead.before T (d+2)) (.input i)) = _
  rw [TailPrecompose.left_input]
  rfl

theorem closed_input_succ (i : Fin (m₁+m₂)) :
    (closedFamily d T V).ports (.input ⟨i.val+1,by simp⟩) = .input ⟨i.val+1,by simp⟩ := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  have index : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports
      (.input ⟨i.val,by simp⟩) = .input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m₁+m₂) Wire.term).length) :=
    congrArg Port.input (Fin.ext (Nat.add_comm _ _))
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T V) (remaining d T V) (selected_remaining_disjoint d T V)).ports (.input (⟨i.val+1,by simp⟩ : Fin ([Wire.term]++List.replicate (m₁+m₂) Wire.term).length)) = _
  rw [← index,Occurrence.tensorJoin_right,remaining_input]

theorem argument_output (i : Fin O.length) : (argument d T V).ports (.output i) = .output i := by
  let j : Fin ([Wire.term]++O).length := ⟨1+i.val,by simp; omega⟩
  have original : (argument d T V).ports (.output i) = (inserted d T V).ports (.output j) := by
    apply congrArg (inserted d T V).ports
    change BoundarySerial.rightInsert (primitiveNet (d+2) (.operation .app))
      (Net.Tensor.net (smallLeft (d+1)) V) (.output j) = .output j
    exact Application.right_serial_output _ _ _
  rw [original]
  apply CompleteMatchCut.replace_output
  have index : (BoxPullWeakening.ReverseComponents.tensorRight (primitiveNet (d+2) (.operation (.unary .deref)))
      (SmallFamilyApplication.discarded d V)).ports (.output i) = .output j := rfl
  change (BoxPullWeakening.ReverseComponents.tensorJoin (SmallFamilyApplication.reader d T V)
    (SmallFamilyApplication.argumentOccurrence d T V) (SmallFamilyApplication.body_disjoint d T V)).ports (.output j) = _
  rw [← index,Occurrence.tensorJoin_right]
  change (Port.output (Net.Tensor.join [] O ⟨true,i⟩) : (SmallFamilyApplication.opened d T V).Vertex) = .output i
  exact congrArg Port.output (Fin.ext (Nat.zero_add _))

/-- The generic original application context is realized by its actual head,
whole original private family, and unchanged arbitrary stable argument. -/
noncomputable def sourceOccurrence : Occurrence
    ((ApplyFirst.net (closedGraph d T) V).reboundary (List.append_nil _).symm rfl) (host d T V) :=
  (ApplyFirst.Join.occurrence (closedGraph d T) V (head d T V) (closedFamily d T V) (argument d T V)
    (head_function d T V) (head_argument d T V) (head_family_disjoint d T V)
    (head_argument_disjoint d T V) (family_argument_disjoint d T V)).reboundarySource _ _

theorem input (i : Fin (List.replicate ((m₁+m₂)+1) Wire.term ++ []).length) :
    (sourceOccurrence d T V).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    rw [eq]
    change (ApplyFirst.Join.occurrence (closedGraph d T) V (head d T V) (closedFamily d T V) (argument d T V) (head_function d T V) (head_argument d T V) (head_family_disjoint d T V) (head_argument_disjoint d T V) (family_argument_disjoint d T V)).ports (.input ⟨0,by simp⟩) = _
    rw [ApplyFirst.Join.input_zero,head_input]
  · let j : Fin (m₁+m₂) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_append,List.length_replicate,List.length_nil] at h; omega⟩
    have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
    rw [eq]
    change (ApplyFirst.Join.occurrence (closedGraph d T) V (head d T V) (closedFamily d T V) (argument d T V) (head_function d T V) (head_argument d T V) (head_family_disjoint d T V) (head_argument_disjoint d T V) (family_argument_disjoint d T V)).ports (.input ⟨j.val+1,by simp⟩) = _
    rw [ApplyFirst.Join.input_succ,closed_input_succ]

theorem output (i : Fin O.length) : (sourceOccurrence d T V).ports (.output i) = .output i := by
  change (ApplyFirst.Join.occurrence (closedGraph d T) V (head d T V) (closedFamily d T V) (argument d T V) (head_function d T V) (head_argument d T V) (head_family_disjoint d T V) (head_argument_disjoint d T V) (family_argument_disjoint d T V)).ports (.output i) = _
  rw [ApplyFirst.Join.output,argument_output]


theorem covers_head (e : (primitiveNet (d+2) (.operation .app)).Edge) :
    ∃ a, (sourceOccurrence d T V).edges a = (head d T V).edges e := ⟨⟨none,e⟩,rfl⟩
theorem covers_argument (e : V.Edge) :
    ∃ a, (sourceOccurrence d T V).edges a = (argument d T V).edges e := ⟨⟨some true,e⟩,rfl⟩
theorem covers_selected (e : (smallLeft (d+1)).Edge) :
    ∃ a, (sourceOccurrence d T V).edges a = (selected d T V).edges e :=
  ⟨⟨some false,⟨false,⟨false,e⟩⟩⟩,rfl⟩
theorem covers_remaining (e : (leftFamily d m₁ m₂).Edge) :
    ∃ a, (sourceOccurrence d T V).edges a = (remaining d T V).edges e :=
  ⟨⟨some false,⟨false,⟨true,e⟩⟩⟩,rfl⟩
theorem covers_cell (e : (Serial.net (T.atDepth (d+2)) (privateCell (d+2))).Edge) :
    ∃ a, (sourceOccurrence d T V).edges a = (cell d T V).edges e :=
  ⟨⟨some false,⟨true,e⟩⟩,rfl⟩

/-- Before the inverse beta cut, only the actual reader and discarded
argument belong to the removed component; all other edges belong to the
unchanged remaining family or the complete original private cell. -/
theorem opened_cover (e : (SmallFamilyApplication.opened d T V).Edge) :
    (∃ a, (SmallFamilyApplication.bodyOccurrence d T V).edges a = e) ∨
    (∃ a, (oldFamily d T V).edges a = e) ∨
    ∃ a, (oldCell d T V).edges a = e := by
  rcases e with ⟨part,e⟩
  cases part
  · rcases e with ⟨part,e⟩
    cases part
    · exact .inr (.inl ⟨e,rfl⟩)
    · rcases PrivateSource.cover T (d+2) e with eq | ⟨a,eq⟩
      · subst e
        exact .inl ⟨⟨false,(0 : Fin 1)⟩,rfl⟩
      · right; right
        refine ⟨a,?_⟩
        change (SmallFamilyApplication.privateOccurrence d T V).edges
          ((TailPrecompose.rightOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))).edges
            ((PrivateSource.occurrence T (d+2)).edges a)) = _
        rw [eq]
        rfl
  · exact .inl ⟨⟨true,e⟩,rfl⟩

/-- Every actual source edge is covered by the three original components;
this includes all unused sharing siblings and every argument resource edge. -/
theorem cover : Function.Surjective (sourceOccurrence d T V).edges := by
  rintro (⟨e,ne⟩ | e)
  · cases e with
    | none => exact False.elim (ne rfl)
    | some retained =>
      obtain ⟨e,avoid⟩ := retained
      rcases opened_cover d T V e with ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩
      · exact False.elim (avoid a eq)
      · obtain ⟨x,h⟩ := covers_remaining d T V a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
      · obtain ⟨x,h⟩ := covers_cell d T V a
        refine ⟨x,h.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        apply Subtype.ext
        exact eq
  · rcases e with ⟨part,e⟩
    cases part
    · exact covers_head d T V e
    · rcases e with ⟨part,e⟩
      cases part
      · exact covers_selected d T V e
      · exact covers_argument d T V e

/-- The complete source is the original application context around the
entire original Figure20 family, with only equal-interface presentation casts.
The map fixes every external input and argument output. -/
noncomputable def iso : DeepIso
    ((ApplyFirst.net (closedGraph d T) V).reboundary (List.append_nil _).symm rfl)
    (SmallFamilyApplication.before d T V) :=
  (sourceOccurrence d T V).iso_of_edge_surjective (input d T V) (output d T V) (cover d T V)

end Hypernets.Copying.Parametricity.SmallFamilySource
