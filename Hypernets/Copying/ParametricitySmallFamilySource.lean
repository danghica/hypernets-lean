import Hypernets.Copying.ParametricitySmallFamilyApplication
import Hypernets.Copying.ParametricityPrivateSource
import Hypernets.Copying.ParametricityIsolatedFamily

/-! The computed smaller-beta predecessor contains the entire original
isolated Figure20 family, its arbitrary original private tree, and its literal
allocated cell. The only external components are application and argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallFamilySource
open Graph Opening Combined
variable {m₁ m₂ O} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))
    (V : Hypernet (d+2) [.term] O)

noncomputable abbrev host := SmallFamilyApplication.before d T V
abbrev localSource := Application.before (readBody (d+1)) V
noncomputable def inserted : Occurrence (localSource d V) (host d T V) :=
  (SmallFamilyApplication.bodyOccurrence d T V).replacement (localSource d V)
noncomputable def head :=
  (BoxPullWeakening.ReverseComponents.serialLeft (primitiveNet (d+2) (.operation .app))
    (Net.Tensor.net (smallLeft (d+1)) V)).comp (inserted d T V)
noncomputable def arguments :=
  (BoxPullWeakening.ReverseComponents.serialRight (primitiveNet (d+2) (.operation .app))
    (Net.Tensor.net (smallLeft (d+1)) V)).comp (inserted d T V)
noncomputable def selected :=
  (BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) V).comp (arguments d T V)
noncomputable def argument :=
  (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) V).comp (arguments d T V)

noncomputable def oldFamily : Occurrence (leftFamily d m₁ m₂) (SmallFamilyApplication.opened d T V) :=
  (TailPrecompose.leftOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))).comp
    (SmallFamilyApplication.privateOccurrence d T V)
noncomputable def oldCell : Occurrence (Serial.net (T.atDepth (d+2)) (privateCell (d+2)))
    (SmallFamilyApplication.opened d T V) :=
  ((PrivateSource.occurrence T (d+2)).comp
    (TailPrecompose.rightOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2)))).comp
      (SmallFamilyApplication.privateOccurrence d T V)

theorem family_avoids : ∀ e a,
    (SmallFamilyApplication.bodyOccurrence d T V).edges e ≠ (oldFamily d T V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part <;> cases eq

theorem cell_avoids : ∀ e a,
    (SmallFamilyApplication.bodyOccurrence d T V).edges e ≠ (oldCell d T V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · change (SmallFamilyApplication.reader d T V).edges e =
      (SmallFamilyApplication.privateOccurrence d T V).edges
        ((TailPrecompose.rightOccurrence (leftFamily d m₁ m₂) (PrivateRead.before T (d+2))).edges
          ((PrivateSource.combined T (d+2)).edges ((PrivateSource.source_iso T (d+2)).edges.toFun a))) at eq
    generalize (PrivateSource.source_iso T (d+2)).edges.toFun a = x at eq
    obtain ⟨part,x⟩ := x
    cases part <;> cases eq
  · cases eq

noncomputable def remaining : Occurrence (leftFamily d m₁ m₂) (host d T V) :=
  (SmallFamilyApplication.bodyOccurrence d T V).acrossCut (oldFamily d T V)
    (family_avoids d T V) (localSource d V)
noncomputable def cell : Occurrence (Serial.net (T.atDepth (d+2)) (privateCell (d+2))) (host d T V) :=
  (SmallFamilyApplication.bodyOccurrence d T V).acrossCut (oldCell d T V)
    (cell_avoids d T V) (localSource d V)

theorem selected_remaining_disjoint : ∀ e a, (selected d T V).edges e ≠ (remaining d T V).edges a := by
  intro e a eq
  cases eq

noncomputable def family : Occurrence (IsolatedFamily.smallLeftFamily d m₁ m₂) (host d T V) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T V) (remaining d T V)
    (selected_remaining_disjoint d T V)).reboundarySource _ _

/-- Before beta, the selected lambda's free x is exactly the original private
reader attachment reconstructed by the inverse beta cut. -/
theorem selected_cell : (selected d T V).ports (.output (0 : Fin 1)) =
    (cell d T V).ports (.input ⟨0,by simp⟩) := by
  have link : (oldCell d T V).ports (.input ⟨0,by simp⟩) =
      (SmallFamilyApplication.bodyOccurrence d T V).ports (.output (⟨0,by simp⟩ : Fin ([Wire.term]++O).length)) := by
    change (SmallFamilyApplication.privateOccurrence d T V).ports
      ((TailPrecompose.rightOccurrence _ _).ports ((PrivateSource.occurrence T (d+2)).ports (.input ⟨0,by simp⟩))) = _
    rw [PrivateSource.selected_input]
    rfl
  have actual := (SmallFamilyApplication.bodyOccurrence d T V).acrossCut_replacement_output
    (localSource d V) (oldCell d T V) (cell_avoids d T V) (.input ⟨0,by simp⟩)
    (⟨0,by simp⟩ : Fin ([Wire.term]++O).length) link
  change (cell d T V).ports (.input ⟨0,by simp⟩) =
    (inserted d T V).ports (.output (⟨0,by simp⟩ : Fin ([Wire.term]++O).length)) at actual
  have closure : (selected d T V).ports (.output (0 : Fin 1)) =
      (inserted d T V).ports (.output (⟨0,by simp⟩ : Fin ([Wire.term]++O).length)) := by
    apply congrArg (inserted d T V).ports
    change BoundarySerial.rightInsert (primitiveNet (d+2) (.operation .app)) (Net.Tensor.net (smallLeft (d+1)) V) (.output ⟨0,by simp⟩) = _
    exact Application.right_serial_output _ _ _
  exact closure.trans actual.symm

theorem remaining_cell (i : Fin (m₁+m₂)) :
    (remaining d T V).ports (.output ⟨i.val,by simp⟩) =
      (cell d T V).ports (.input ⟨i.val+1,by simp⟩) := by
  have link : (oldFamily d T V).ports (.output ⟨i.val,by simp⟩) =
      (oldCell d T V).ports (.input ⟨i.val+1,by simp⟩) := by
    change (SmallFamilyApplication.privateOccurrence d T V).ports
      ((TailPrecompose.leftOccurrence _ _).ports (.output ⟨i.val,by simp⟩)) =
      (SmallFamilyApplication.privateOccurrence d T V).ports
        ((TailPrecompose.rightOccurrence _ _).ports ((PrivateSource.occurrence T (d+2)).ports (.input ⟨i.val+1,by simp⟩)))
    rw [PrivateSource.remaining_input]
    exact congrArg (SmallFamilyApplication.privateOccurrence d T V).ports
      (TailPrecompose.right_succ (leftFamily d m₁ m₂) (PrivateRead.before T (d+2)) i).symm
  exact (SmallFamilyApplication.bodyOccurrence d T V).acrossCut_link (localSource d V)
    (oldFamily d T V) (oldCell d T V) (family_avoids d T V) (cell_avoids d T V) _ _ link


theorem family_cell (i : Fin (List.replicate ((m₁+m₂)+1) Wire.term).length) :
    (family d T V).ports (.output i) = (cell d T V).ports (.input i) := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    subst i
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T V) (remaining d T V) (selected_remaining_disjoint d T V)).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports (.output (0 : Fin 1))) = _
    rw [Occurrence.tensorJoin_left]
    exact selected_cell d T V
  · let j : Fin (m₁+m₂) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
    have eq : (BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports
        (.output ⟨j.val,by simp⟩) = .output (⟨i.val,by have h:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_cons,List.length_nil] at *; omega⟩ : Fin ([Wire.term]++List.replicate (m₁+m₂) Wire.term).length) := by
      exact congrArg Port.output (Fin.ext (by change 1+j.val=i.val; dsimp [j]; omega))
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T V) (remaining d T V) (selected_remaining_disjoint d T V)).ports (.output _) = _
    rw [← eq,Occurrence.tensorJoin_right,remaining_cell]
    exact congrArg (cell d T V).ports (congrArg Port.input (Fin.ext (by dsimp [j]; omega)))

theorem family_cell_disjoint : ∀ e a, (family d T V).edges e ≠ (cell d T V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · cases eq
  · have old := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val (Sum.inl.inj eq)))
    change (oldFamily d T V).edges e = (oldCell d T V).edges a at old
    cases old

abbrev closedGraph := Serial.net (IsolatedFamily.smallLeftFamily d m₁ m₂)
  (Serial.net (T.atDepth (d+2)) (privateCell (d+2)))

/-- Every original family abstraction, the entire arbitrary T, and the
unchanged allocated cell constitute one complete actual source occurrence. -/
noncomputable def closedFamily : Occurrence (closedGraph d T) (host d T V) :=
  Occurrence.SerialJoin.occurrence (family d T V) (cell d T V)
    (family_cell d T V) (family_cell_disjoint d T V)

theorem closed_zero : (closedFamily d T V).ports (.input ⟨0,by simp⟩) =
    (selected d T V).ports (.input (0 : Fin 1)) := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d T V) (remaining d T V) (selected_remaining_disjoint d T V)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (leftFamily d m₁ m₂)).ports (.input (0 : Fin 1))) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem head_function : (head d T V).ports (.output (0 : Fin 2)) =
    (closedFamily d T V).ports (.input ⟨0,by simp⟩) := by
  rw [closed_zero]
  rfl

theorem head_argument : (head d T V).ports (.output (1 : Fin 2)) =
    (argument d T V).ports (.input (0 : Fin 1)) := by rfl

theorem head_family_disjoint : ∀ e a, (head d T V).edges e ≠ (closedFamily d T V).edges a := by
  rintro e ⟨part,a⟩ eq
  cases part
  · rcases a with ⟨part,a⟩
    cases part <;> cases eq
  · cases eq

theorem head_argument_disjoint : ∀ e a, (head d T V).edges e ≠ (argument d T V).edges a := by
  intro e a eq; cases eq

theorem family_argument_disjoint : ∀ e a, (closedFamily d T V).edges e ≠ (argument d T V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · rcases e with ⟨part,e⟩
    cases part <;> cases eq
  · cases eq

/-- The isolated source family is certified by the actual original
parametricity pre-template, after the proved explicit input permutation. -/
noncomputable def familyWitness : FillingWitness template (closedGraph d T)
    (IsolatedFamily.smallRightFamily d m₁ m₂) :=
  (IsolatedFamily.smallWitness d T).congr
    (Serial.Association.iso (IsolatedFamily.smallLeftFamily d m₁ m₂)
      (T.atDepth (d+2)) (privateCell (d+2))) (DeepIso.refl _)

end Hypernets.Copying.Parametricity.SmallFamilySource
