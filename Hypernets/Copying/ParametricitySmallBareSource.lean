import Hypernets.Copying.ParametricitySmallBareApplication
import Hypernets.Copying.ParametricityPrivateSource
import Hypernets.Copying.ParametricityIsolatedFamily

/-! The computed smaller-beta predecessor contains the entire original
isolated Figure20 family, its arbitrary original private tree, and its literal
allocated cell. The only external components are application and argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallBareSource
open Graph Opening Combined
variable {m₁ m₂} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))

noncomputable abbrev host := SmallBareApplication.before d T
abbrev localSource := Application.RetainedFrame.net (readBody (d+1))
noncomputable def inserted : Occurrence (localSource d) (host d T) :=
  (SmallBareApplication.bodyOccurrence d T).replacement (localSource d)
noncomputable def head : Occurrence (primitiveNet (d+2) (.operation .app)) (host d T) := (Application.RetainedFrame.appOccurrence (readBody (d+1))).comp (inserted d T)
noncomputable def selected : Occurrence (smallLeft (d+1)) (host d T) := (Application.RetainedFrame.closureOccurrence (readBody (d+1))).comp (inserted d T)

noncomputable def oldFamily : Occurrence (leftFamily d m₁ m₂) (SmallBareApplication.opened d T) :=
  (TailPrecompose.leftOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))).comp
    (SmallBareApplication.privateOccurrence d T)
noncomputable def oldCell : Occurrence (Serial.net (T.atDepth (d+2)) (privateCell (d+2)))
    (SmallBareApplication.opened d T) :=
  ((PrivateSource.occurrence T (d+2)).comp
    (TailPrecompose.rightOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2)))).comp
      (SmallBareApplication.privateOccurrence d T)

theorem family_avoids : ∀ e a,
    (SmallBareApplication.bodyOccurrence d T).edges e ≠ (oldFamily d T).edges a := by
  intro e a eq
  change (BoxPullWeakening.AdjoinOccurrence.components _ .term (SmallBareApplication.reader d T)
    (SmallBareApplication.weakeningOccurrence d T) ((SmallBareApplication.bodyIso d).edges.toFun e).1).edges
      ((SmallBareApplication.bodyIso d).edges.toFun e).2 = _ at eq
  generalize (SmallBareApplication.bodyIso d).edges.toFun e = x at eq
  obtain ⟨part,e⟩ := x
  cases part <;> cases eq

theorem cell_avoids : ∀ e a,
    (SmallBareApplication.bodyOccurrence d T).edges e ≠ (oldCell d T).edges a := by
  intro e a eq
  change (BoxPullWeakening.AdjoinOccurrence.components _ .term (SmallBareApplication.reader d T)
    (SmallBareApplication.weakeningOccurrence d T) ((SmallBareApplication.bodyIso d).edges.toFun e).1).edges
      ((SmallBareApplication.bodyIso d).edges.toFun e).2 = _ at eq
  generalize (SmallBareApplication.bodyIso d).edges.toFun e = x at eq
  obtain ⟨part,e⟩ := x
  cases part
  · change (SmallBareApplication.reader d T).edges e =
      (SmallBareApplication.privateOccurrence d T).edges
        ((TailPrecompose.rightOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))).edges
          ((PrivateSource.combined T (d+2)).edges ((PrivateSource.source_iso T (d+2)).edges.toFun a))) at eq
    generalize (PrivateSource.source_iso T (d+2)).edges.toFun a = x at eq
    obtain ⟨part,x⟩ := x
    cases part <;> cases eq
  · cases eq

noncomputable def remaining : Occurrence (leftFamily d m₁ m₂) (host d T) :=
  (SmallBareApplication.bodyOccurrence d T).acrossCut (oldFamily d T)
    (family_avoids d T) (localSource d)
noncomputable def cell : Occurrence (Serial.net (T.atDepth (d+2)) (privateCell (d+2))) (host d T) :=
  (SmallBareApplication.bodyOccurrence d T).acrossCut (oldCell d T)
    (cell_avoids d T) (localSource d)

theorem selected_remaining_disjoint : ∀ e a, (selected d T).edges e ≠ (remaining d T).edges a := by
  intro e a eq
  cases eq

noncomputable def family : Occurrence (IsolatedFamily.smallLeftFamily d m₁ m₂) (host d T) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T) (remaining d T)
    (selected_remaining_disjoint d T)).reboundarySource _ _

/-- Before beta, the selected lambda's free x is exactly the original private
reader attachment reconstructed by the inverse beta cut. -/
theorem selected_cell : (selected d T).ports (.output (0 : Fin 1)) =
    (cell d T).ports (.input ⟨0,by simp⟩) := by
  have link : (oldCell d T).ports (.input ⟨0,by simp⟩) =
      (SmallBareApplication.bodyOccurrence d T).ports (.output 1) := by
    rw [SmallBareApplication.body_free]
    change (SmallBareApplication.privateOccurrence d T).ports
      ((TailPrecompose.rightOccurrence _ _).ports ((PrivateSource.occurrence T (d+2)).ports (.input ⟨0,by simp⟩))) = _
    rw [PrivateSource.selected_input]
    rfl
  have actual := (SmallBareApplication.bodyOccurrence d T).acrossCut_replacement_output
    (localSource d) (oldCell d T) (cell_avoids d T) (.input ⟨0,by simp⟩) (1 : Fin 2) link
  change (cell d T).ports (.input ⟨0,by simp⟩) = (inserted d T).ports (.output 1) at actual
  exact actual.symm

theorem remaining_cell (i : Fin (m₁+m₂)) :
    (remaining d T).ports (.output ⟨i.val,by simp⟩) =
      (cell d T).ports (.input ⟨i.val+1,by simp⟩) := by
  have link : (oldFamily d T).ports (.output ⟨i.val,by simp⟩) =
      (oldCell d T).ports (.input ⟨i.val+1,by simp⟩) := by
    change (SmallBareApplication.privateOccurrence d T).ports
      ((TailPrecompose.leftOccurrence _ _).ports (.output ⟨i.val,by simp⟩)) =
      (SmallBareApplication.privateOccurrence d T).ports
        ((TailPrecompose.rightOccurrence _ _).ports ((PrivateSource.occurrence T (d+2)).ports (.input ⟨i.val+1,by simp⟩)))
    rw [PrivateSource.remaining_input]
    exact congrArg (SmallBareApplication.privateOccurrence d T).ports
      (TailPrecompose.right_succ (leftFamily d m₁ m₂) (PrivateRead.before T (d+2)) i).symm
  exact (SmallBareApplication.bodyOccurrence d T).acrossCut_link (localSource d)
    (oldFamily d T) (oldCell d T) (family_avoids d T) (cell_avoids d T) _ _ link


theorem family_cell (i : Fin (List.replicate ((m₁+m₂)+1) Wire.term).length) :
    (family d T).ports (.output i) = (cell d T).ports (.input i) := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    subst i
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T) (remaining d T) (selected_remaining_disjoint d T)).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports (.output (0 : Fin 1))) = _
    rw [Occurrence.tensorJoin_left]
    exact selected_cell d T
  · let j : Fin (m₁+m₂) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
    have eq : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports
        (.output ⟨j.val,by simp⟩) = .output (⟨i.val,by have h:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_cons,List.length_nil] at *; omega⟩ : Fin ([Wire.term]++List.replicate (m₁+m₂) Wire.term).length) := by
      exact congrArg Port.output (Fin.ext (by change 1+j.val=i.val; dsimp [j]; omega))
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T) (remaining d T) (selected_remaining_disjoint d T)).ports (.output _) = _
    rw [← eq,Occurrence.tensorJoin_right,remaining_cell]
    exact congrArg (cell d T).ports (congrArg Port.input (Fin.ext (by dsimp [j]; omega)))

theorem family_cell_disjoint : ∀ e a, (family d T).edges e ≠ (cell d T).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · cases eq
  · have old := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val (Sum.inl.inj eq)))
    change (oldFamily d T).edges e = (oldCell d T).edges a at old
    cases old

abbrev closedGraph := Serial.net (IsolatedFamily.smallLeftFamily d m₁ m₂)
  (Serial.net (T.atDepth (d+2)) (privateCell (d+2)))

/-- Every original family abstraction, the entire arbitrary T, and the
unchanged allocated cell constitute one complete actual source occurrence. -/
noncomputable def closedFamily : Occurrence (closedGraph d T) (host d T) :=
  Occurrence.SerialJoin.occurrence (family d T) (cell d T)
    (family_cell d T) (family_cell_disjoint d T)

theorem closed_zero : (closedFamily d T).ports (.input ⟨0,by simp⟩) =
    (selected d T).ports (.input (0 : Fin 1)) := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T) (remaining d T) (selected_remaining_disjoint d T)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports (.input (0 : Fin 1))) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem head_function : (head d T).ports (.output (0 : Fin 2)) =
    (closedFamily d T).ports (.input ⟨0,by simp⟩) := by
  rw [closed_zero]
  rfl

theorem head_family_disjoint : ∀ e a, (head d T).edges e ≠ (closedFamily d T).edges a := by
  rintro e ⟨part,a⟩ eq
  cases part
  · rcases a with ⟨part,a⟩
    cases part
    · rcases a with ⟨part,a⟩
      cases part <;> cases eq
    · cases eq
  · cases eq

/-- The isolated source family is certified by the actual original
parametricity pre-template, after the proved explicit input permutation. -/
noncomputable def familyWitness : FillingWitness template (closedGraph d T)
    (IsolatedFamily.smallRightFamily d m₁ m₂) :=
  (IsolatedFamily.smallWitness d T).congr
    (Serial.Association.iso (IsolatedFamily.smallLeftFamily d m₁ m₂)
      (T.atDepth (d+2)) (privateCell (d+2))) (DeepIso.refl _)

end Hypernets.Copying.Parametricity.SmallBareSource
