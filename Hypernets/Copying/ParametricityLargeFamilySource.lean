import Hypernets.Copying.ParametricityLargeFamilyApplication
import Hypernets.Copying.ParametricityIsolatedFamily
import Hypernets.Copying.ParametricitySerialAssociation
import Hypernets.Copying.OccurrenceAcrossCut
import Hypernets.Copying.BoxPullContractionCutLinks

/-! The computed larger-beta predecessor contains the entire original
isolated Figure20 large family, its arbitrary original private tree, and its literal
allocated cell. The only external components are application and argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeFamilySource
open Graph Opening Combined
variable {m n O} (d : Nat) (C : ContractionTree .term ((m+n)+1))
    (V : Hypernet (d+2) [.term] O)

noncomputable abbrev host := LargeFamilyApplication.leftBefore d C V
abbrev localSource := Application.before (callReadBody d) V
noncomputable def inserted : Occurrence (localSource d V) (host d C V) :=
  (LargeFamilyApplication.leftOpened d C V).replacement (localSource d V)
noncomputable def head :=
  (BoxPullWeakening.ReverseComponents.serialLeft (primitiveNet (d+2) (.operation .app))
    (Net.Tensor.net (largeLeft d) V)).comp (inserted d C V)
noncomputable def arguments :=
  (BoxPullWeakening.ReverseComponents.serialRight (primitiveNet (d+2) (.operation .app))
    (Net.Tensor.net (largeLeft d) V)).comp (inserted d C V)
noncomputable def selected :=
  (BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) V).comp (arguments d C V)
noncomputable def argument :=
  (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) V).comp (arguments d C V)

noncomputable def privateFamily := ApplyFirst.family (IsolatedFamily.smallClosed d C) (LargeOpening.invocation V)
noncomputable def oldFamily : Occurrence (leftFamily d m n) (LargeFamilyApplication.leftAfter d C V) :=
  ((((BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m n)).reboundaryTarget _ _).comp
    (BoxPullWeakening.ReverseComponents.serialLeft (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2)))).comp
      (BoxPullWeakening.ReverseComponents.serialLeft
        (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2)))).comp
          (privateFamily d C V)
noncomputable def oldTree : Occurrence (C.atDepth (d+2)) (LargeFamilyApplication.leftAfter d C V) :=
  ((BoxPullWeakening.ReverseComponents.serialRight (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))).comp
    (BoxPullWeakening.ReverseComponents.serialLeft
      (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2)))).comp
        (privateFamily d C V)
noncomputable def oldStore : Occurrence (privateCell (d+2)) (LargeFamilyApplication.leftAfter d C V) :=
  (BoxPullWeakening.ReverseComponents.serialRight
    (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))).comp
      (privateFamily d C V)

theorem tree_store_link : ∀ i, (oldTree d C V).ports (.output i) = (oldStore d C V).ports (.input i) := by
  intro i
  change Fin 1 at i
  have zero : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rfl

theorem tree_store_disjoint : ∀ e a, (oldTree d C V).edges e ≠ (oldStore d C V).edges a := by
  intro e a eq
  cases eq

noncomputable def oldCell : Occurrence (Serial.net (C.atDepth (d+2)) (privateCell (d+2)))
    (LargeFamilyApplication.leftAfter d C V) :=
  Occurrence.SerialJoin.occurrence (oldTree d C V) (oldStore d C V)
    (tree_store_link d C V) (tree_store_disjoint d C V)

theorem family_avoids : ∀ e a,
    (LargeFamilyApplication.leftOpened d C V).edges e ≠ (oldFamily d C V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · cases eq
  · obtain ⟨part,e⟩ := e
    cases part <;> cases eq

theorem cell_avoids : ∀ e a,
    (LargeFamilyApplication.leftOpened d C V).edges e ≠ (oldCell d C V).edges a := by
  rintro ⟨part,e⟩ ⟨side,a⟩ eq
  cases part
  · cases side <;> cases eq
  · obtain ⟨part,e⟩ := e
    cases part <;> cases side <;> cases eq

noncomputable def remaining : Occurrence (leftFamily d m n) (host d C V) :=
  (LargeFamilyApplication.leftOpened d C V).acrossCut (oldFamily d C V)
    (family_avoids d C V) (localSource d V)
noncomputable def cell : Occurrence (Serial.net (C.atDepth (d+2)) (privateCell (d+2))) (host d C V) :=
  (LargeFamilyApplication.leftOpened d C V).acrossCut (oldCell d C V)
    (cell_avoids d C V) (localSource d V)

theorem selected_remaining_disjoint : ∀ e a, (selected d C V).edges e ≠ (remaining d C V).edges a := by
  intro e a eq
  cases eq

noncomputable def family : Occurrence (IsolatedFamily.largeLeftFamily d m n) (host d C V) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C V) (remaining d C V)
    (selected_remaining_disjoint d C V)).reboundarySource _ _

theorem selected_cell : (selected d C V).ports (.output (0 : Fin 1)) =
    (cell d C V).ports (.input ⟨0,by simp⟩) := by
  have link : (oldCell d C V).ports (.input ⟨0,by simp⟩) =
      (LargeFamilyApplication.leftOpened d C V).ports (.output (⟨0,by simp⟩ : Fin ([Wire.term]++O).length)) := by
    rw [oldCell,Occurrence.SerialJoin.occurrence_input]
    change _ = (ApplyFirst.binaryOccurrence _ _ _).ports (.output _)
    rw [ApplyFirst.binaryOccurrence,Occurrence.SerialJoin.occurrence_output]
    change _ = (BoxPullWeakening.ReverseComponents.tensorJoin _ _ _).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (LargeOpening.invocation V)).ports (.output (0 : Fin 1)))
    rw [Occurrence.tensorJoin_left]
    rfl
  have actual := (LargeFamilyApplication.leftOpened d C V).acrossCut_replacement_output
    (localSource d V) (oldCell d C V) (cell_avoids d C V) (.input ⟨0,by simp⟩)
    (⟨0,by simp⟩ : Fin ([Wire.term]++O).length) link
  change (cell d C V).ports (.input ⟨0,by simp⟩) =
    (inserted d C V).ports (.output (⟨0,by simp⟩ : Fin ([Wire.term]++O).length)) at actual
  have closure : (selected d C V).ports (.output (0 : Fin 1)) =
      (inserted d C V).ports (.output (⟨0,by simp⟩ : Fin ([Wire.term]++O).length)) := by
    apply congrArg (inserted d C V).ports
    change BoundarySerial.rightInsert (primitiveNet (d+2) (.operation .app)) (Net.Tensor.net (largeLeft d) V) (.output ⟨0,by simp⟩) = _
    exact Application.right_serial_output _ _ _
  exact closure.trans actual.symm

theorem remaining_cell (i : Fin (m+n)) :
    (remaining d C V).ports (.output ⟨i.val,by simp⟩) =
      (cell d C V).ports (.input ⟨i.val+1,by simp⟩) := by
  have link : (oldFamily d C V).ports (.output ⟨i.val,by simp⟩) =
      (oldCell d C V).ports (.input ⟨i.val+1,by simp⟩) := by
    rw [oldCell,Occurrence.SerialJoin.occurrence_input]
    apply congrArg (privateFamily d C V).ports
    dsimp only [Occurrence.comp,Function.comp_apply]
    apply congrArg (BoxPullWeakening.ReverseComponents.serialLeft
      (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))).ports
    change BoundarySerial.leftInsert (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2)) (.output ⟨1+i.val,by simp;omega⟩) =
      BoundarySerial.rightInsert (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2)) (.input ⟨i.val+1,by simp⟩)
    have indices : (⟨1+i.val,by simp;omega⟩ : Fin (List.replicate ((m+n)+1) Wire.term).length) =
        ⟨i.val+1,by simp⟩ := Fin.ext (Nat.add_comm _ _)
    rw [indices]
    simp [BoundarySerial.leftInsert,BoundarySerial.rightInsert,Net.Expansion.insert,
      Serial.pattern,Serial.filling,Net.targetPort,Net.sourcePort,Net.Expansion.host,Port.map]
  exact (LargeFamilyApplication.leftOpened d C V).acrossCut_link (localSource d V)
    (oldFamily d C V) (oldCell d C V) (family_avoids d C V) (cell_avoids d C V) _ _ link

/-- Before beta the selected large lambda retains exactly its original private
variable attachment, although its callback is not part of the private tree. -/
theorem family_cell (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (family d C V).ports (.output i) = (cell d C V).ports (.input i) := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    subst i
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C V) (remaining d C V) (selected_remaining_disjoint d C V)).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) (leftFamily d m n)).ports (.output (0 : Fin 1))) = _
    rw [Occurrence.tensorJoin_left]
    exact selected_cell d C V
  · let j : Fin (m+n) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
    have eq : (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (leftFamily d m n)).ports
        (.output ⟨j.val,by simp⟩) = .output (⟨i.val,by have h:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_cons,List.length_nil] at *; omega⟩ : Fin ([Wire.term]++List.replicate (m+n) Wire.term).length) := by
      exact congrArg Port.output (Fin.ext (by change 1+j.val=i.val; dsimp [j]; omega))
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C V) (remaining d C V) (selected_remaining_disjoint d C V)).ports (.output _) = _
    rw [← eq,Occurrence.tensorJoin_right,remaining_cell]
    exact congrArg (cell d C V).ports (congrArg Port.input (Fin.ext (by dsimp [j]; omega)))

theorem family_cell_disjoint : ∀ e a, (family d C V).edges e ≠ (cell d C V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · cases eq
  · have old := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val (Sum.inl.inj eq)))
    change (oldFamily d C V).edges e = (oldCell d C V).edges a at old
    obtain ⟨side,a⟩ := a
    cases side <;> cases old

abbrev closedGraph := Serial.net (IsolatedFamily.largeLeftFamily d m n)
  (Serial.net (C.atDepth (d+2)) (privateCell (d+2)))

/-- Every original family abstraction, the entire arbitrary C, and the
unchanged allocated cell constitute one complete actual source occurrence. -/
noncomputable def closedFamily : Occurrence (closedGraph d C) (host d C V) :=
  Occurrence.SerialJoin.occurrence (family d C V) (cell d C V)
    (family_cell d C V) (family_cell_disjoint d C V)

theorem closed_zero : (closedFamily d C V).ports (.input ⟨0,by simp⟩) =
    (selected d C V).ports (.input (0 : Fin 1)) := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C V) (remaining d C V) (selected_remaining_disjoint d C V)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) (leftFamily d m n)).ports (.input (0 : Fin 1))) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem head_function : (head d C V).ports (.output (0 : Fin 2)) =
    (closedFamily d C V).ports (.input ⟨0,by simp⟩) := by
  rw [closed_zero]
  rfl

theorem head_argument : (head d C V).ports (.output (1 : Fin 2)) =
    (argument d C V).ports (.input (0 : Fin 1)) := by rfl

theorem head_family_disjoint : ∀ e a, (head d C V).edges e ≠ (closedFamily d C V).edges a := by
  rintro e ⟨part,a⟩ eq
  cases part
  · rcases a with ⟨part,a⟩
    cases part <;> cases eq
  · cases eq

theorem head_argument_disjoint : ∀ e a, (head d C V).edges e ≠ (argument d C V).edges a := by
  intro e a eq; cases eq

theorem family_argument_disjoint : ∀ e a, (closedFamily d C V).edges e ≠ (argument d C V).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · rcases e with ⟨part,e⟩
    cases part <;> cases eq
  · cases eq

/-- Che isolated source family is certified by the actual original
parametricity pre-template, after the proved explicit input permutation. -/
noncomputable def familyWitness : FillingWitness template (closedGraph d C)
    (IsolatedFamily.largeRightFamily d m n) :=
  (IsolatedFamily.largeWitness d C).congr
    (Serial.Association.iso (IsolatedFamily.largeLeftFamily d m n)
      (C.atDepth (d+2)) (privateCell (d+2))) (DeepIso.refl _)

end Hypernets.Copying.Parametricity.LargeFamilySource
