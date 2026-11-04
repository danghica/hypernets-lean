import Hypernets.Copying.ParametricityLargeBareApplication
import Hypernets.Copying.RetainedBetaPorts
import Hypernets.Copying.ParametricityIsolatedFamily
import Hypernets.Copying.ParametricitySerialAssociation
import Hypernets.Copying.OccurrenceAcrossCut
import Hypernets.Copying.BoxPullContractionCutLinks

/-! The computed larger-beta predecessor contains the entire original
isolated Figure20 large family, its arbitrary original private tree, and its literal
allocated cell. The argument remains an exposed wire; no argument edge is included. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeBareSource
open Graph Opening Combined Application
variable {m n} (d : Nat) (C : ContractionTree .term ((m+n)+1))

noncomputable abbrev host := LargeBareApplication.leftBefore d C
abbrev localSource := RetainedFrame.net (callReadBody d)
noncomputable def inserted : Occurrence (localSource d) (host d C) :=
  (LargeBareApplication.leftBody d C).replacement (localSource d)
noncomputable def head := (RetainedFrame.appOccurrence (callReadBody d)).comp (inserted d C)
noncomputable def selected : Occurrence (largeLeft d) (host d C) := (RetainedFrame.closureOccurrence (callReadBody d)).comp (inserted d C)

noncomputable def privateFamily := (BareApplyFirst.family (IsolatedFamily.smallClosed d C)).comp
  (BareCall.firstBlock (IsolatedFamily.smallClosed d C) (callback (d+2)))
noncomputable def oldFamily : Occurrence (leftFamily d m n) (LargeBareApplication.leftAfter d C) :=
  ((((BoxPullWeakening.ReverseComponents.tensorRight (smallLeft (d+1)) (leftFamily d m n)).reboundaryTarget _ _).comp
    (BoxPullWeakening.ReverseComponents.serialLeft (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2)))).comp
      (BoxPullWeakening.ReverseComponents.serialLeft
        (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2)))).comp
          (privateFamily d C)
noncomputable def oldTree : Occurrence (C.atDepth (d+2)) (LargeBareApplication.leftAfter d C) :=
  ((BoxPullWeakening.ReverseComponents.serialRight (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))).comp
    (BoxPullWeakening.ReverseComponents.serialLeft
      (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2)))).comp
        (privateFamily d C)
noncomputable def oldStore : Occurrence (privateCell (d+2)) (LargeBareApplication.leftAfter d C) :=
  (BoxPullWeakening.ReverseComponents.serialRight
    (Serial.net (IsolatedFamily.smallLeftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))).comp
      (privateFamily d C)

theorem tree_store_link : ∀ i, (oldTree d C).ports (.output i) = (oldStore d C).ports (.input i) := by
  intro i
  change Fin 1 at i
  have zero : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rfl

theorem tree_store_disjoint : ∀ e a, (oldTree d C).edges e ≠ (oldStore d C).edges a := by
  intro e a eq
  cases eq

noncomputable def oldCell : Occurrence (Serial.net (C.atDepth (d+2)) (privateCell (d+2)))
    (LargeBareApplication.leftAfter d C) :=
  Occurrence.SerialJoin.occurrence (oldTree d C) (oldStore d C)
    (tree_store_link d C) (tree_store_disjoint d C)

theorem family_avoids : ∀ e a,
    (LargeBareApplication.leftBody d C).edges e ≠ (oldFamily d C).edges a := by
  intro e a eq
  change (BareCall.bodyOccurrence (hasPrivate := true) (IsolatedFamily.smallClosed d C) (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C) (LargeFamilyApplication.left_member_input d C)).edges
    ((LargeOpening.read_bodyIso (d := d)).edges.toFun e) = _ at eq
  generalize (LargeOpening.read_bodyIso (d := d)).edges.toFun e = x at eq
  rcases x with ⟨part,x⟩
  cases part
  · cases eq
  · rcases x with ⟨part,x⟩
    cases part <;> cases eq

theorem cell_avoids : ∀ e a,
    (LargeBareApplication.leftBody d C).edges e ≠ (oldCell d C).edges a := by
  intro e a eq
  change (BareCall.bodyOccurrence (hasPrivate := true) (IsolatedFamily.smallClosed d C) (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C) (LargeFamilyApplication.left_member_input d C)).edges
    ((LargeOpening.read_bodyIso (d := d)).edges.toFun e) = _ at eq
  generalize (LargeOpening.read_bodyIso (d := d)).edges.toFun e = x at eq
  rcases x with ⟨part,x⟩
  rcases a with ⟨side,a⟩
  cases part
  · cases side <;> cases eq
  · rcases x with ⟨part,x⟩
    cases part <;> cases side <;> cases eq

noncomputable def remaining : Occurrence (leftFamily d m n) (host d C) :=
  (LargeBareApplication.leftBody d C).acrossCut (oldFamily d C)
    (family_avoids d C) (localSource d)
noncomputable def cell : Occurrence (Serial.net (C.atDepth (d+2)) (privateCell (d+2))) (host d C) :=
  (LargeBareApplication.leftBody d C).acrossCut (oldCell d C)
    (cell_avoids d C) (localSource d)

theorem selected_remaining_disjoint : ∀ e a, (selected d C).edges e ≠ (remaining d C).edges a := by
  intro e a eq
  cases eq

noncomputable def family : Occurrence (IsolatedFamily.largeLeftFamily d m n) (host d C) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C) (remaining d C)
    (selected_remaining_disjoint d C)).reboundarySource _ _

theorem selected_cell : (selected d C).ports (.output (0 : Fin 1)) =
    (cell d C).ports (.input ⟨0,by simp⟩) := by
  have link : (oldCell d C).ports (.input ⟨0,by simp⟩) =
      (LargeBareApplication.leftBody d C).ports (.output (1 : Fin 2)) := by
    rw [oldCell,Occurrence.SerialJoin.occurrence_input]
    change _ = (BareCall.rawOccurrence (hasPrivate := true) (IsolatedFamily.smallClosed d C) (smallLeft (d+1)) (callback (d+2)) (LargeFamilyApplication.leftMember d C) (LargeFamilyApplication.left_member_input d C)).ports (.output (0 : Fin 2))
    rw [BareCall.rawOccurrence,Occurrence.SerialJoin.occurrence_output]
    change _ = (BoxPullWeakening.ReverseComponents.tensorJoin _ _ _).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft (smallLeft (d+1)) (callback (d+2))).ports (.output (0 : Fin 1)))
    rw [Occurrence.tensorJoin_left]
    rfl
  have actual := (LargeBareApplication.leftBody d C).acrossCut_replacement_output
    (localSource d) (oldCell d C) (cell_avoids d C) (.input ⟨0,by simp⟩) (1 : Fin 2) link
  change (cell d C).ports (.input ⟨0,by simp⟩) = (inserted d C).ports (.output (1 : Fin 2)) at actual
  have closure : (selected d C).ports (.output (0 : Fin 1)) =
      (inserted d C).ports (.output (1 : Fin 2)) :=
    congrArg (inserted d C).ports (RetainedFrame.closure_output (callReadBody d) (0 : Fin 1))
  exact closure.trans actual.symm

theorem remaining_cell (i : Fin (m+n)) :
    (remaining d C).ports (.output ⟨i.val,by simp⟩) =
      (cell d C).ports (.input ⟨i.val+1,by simp⟩) := by
  have link : (oldFamily d C).ports (.output ⟨i.val,by simp⟩) =
      (oldCell d C).ports (.input ⟨i.val+1,by simp⟩) := by
    rw [oldCell,Occurrence.SerialJoin.occurrence_input]
    apply congrArg (privateFamily d C).ports
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
  exact (LargeBareApplication.leftBody d C).acrossCut_link (localSource d)
    (oldFamily d C) (oldCell d C) (family_avoids d C) (cell_avoids d C) _ _ link

/-- Before beta the selected large lambda retains exactly its original private
variable attachment, although its callback is not part of the private tree. -/
theorem family_cell (i : Fin (List.replicate ((m+n)+1) Wire.term).length) :
    (family d C).ports (.output i) = (cell d C).ports (.input i) := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    subst i
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C) (remaining d C) (selected_remaining_disjoint d C)).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) (leftFamily d m n)).ports (.output (0 : Fin 1))) = _
    rw [Occurrence.tensorJoin_left]
    exact selected_cell d C
  · let j : Fin (m+n) := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
    have eq : (BoxPullWeakening.ReverseComponents.tensorRight (largeLeft d) (leftFamily d m n)).ports
        (.output ⟨j.val,by simp⟩) = .output (⟨i.val,by have h:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_cons,List.length_nil] at *; omega⟩ : Fin ([Wire.term]++List.replicate (m+n) Wire.term).length) := by
      exact congrArg Port.output (Fin.ext (by change 1+j.val=i.val; dsimp [j]; omega))
    change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C) (remaining d C) (selected_remaining_disjoint d C)).ports (.output _) = _
    rw [← eq,Occurrence.tensorJoin_right,remaining_cell]
    exact congrArg (cell d C).ports (congrArg Port.input (Fin.ext (by dsimp [j]; omega)))

theorem family_cell_disjoint : ∀ e a, (family d C).edges e ≠ (cell d C).edges a := by
  rintro ⟨part,e⟩ a eq
  cases part
  · cases eq
  · have old := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val (Sum.inl.inj eq)))
    change (oldFamily d C).edges e = (oldCell d C).edges a at old
    obtain ⟨side,a⟩ := a
    cases side <;> cases old

abbrev closedGraph := Serial.net (IsolatedFamily.largeLeftFamily d m n)
  (Serial.net (C.atDepth (d+2)) (privateCell (d+2)))

/-- Every original family abstraction, the entire arbitrary C, and the
unchanged allocated cell constitute one complete actual source occurrence. -/
noncomputable def closedFamily : Occurrence (closedGraph d C) (host d C) :=
  Occurrence.SerialJoin.occurrence (family d C) (cell d C)
    (family_cell d C) (family_cell_disjoint d C)

theorem closed_zero : (closedFamily d C).ports (.input ⟨0,by simp⟩) =
    (selected d C).ports (.input (0 : Fin 1)) := by
  rw [closedFamily,Occurrence.SerialJoin.occurrence_input]
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected d C) (remaining d C) (selected_remaining_disjoint d C)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (largeLeft d) (leftFamily d m n)).ports (.input (0 : Fin 1))) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem head_function : (head d C).ports (.output (0 : Fin 2)) =
    (closedFamily d C).ports (.input ⟨0,by simp⟩) := by
  rw [closed_zero]
  rfl

theorem head_family_disjoint : ∀ e a, (head d C).edges e ≠ (closedFamily d C).edges a := by
  rintro e ⟨part,a⟩ eq
  cases part
  · rcases a with ⟨part,a⟩
    cases part
    · change (head d C).edges e = (selected d C).edges a at eq
      rcases a with ⟨part,a⟩
      cases part
      · change (head d C).edges e = (inserted d C).edges
          ((RetainedFrame.closureOccurrence (callReadBody d)).edges
            (Serial.leftEdge _ _ a)) at eq
        rw [RetainedFrame.closure_left_edge] at eq
        cases eq
      · change (head d C).edges e = (inserted d C).edges
          ((RetainedFrame.closureOccurrence (callReadBody d)).edges
            (Serial.rightEdge _ _ a)) at eq
        rw [RetainedFrame.closure_right_edge] at eq
        cases eq
    · cases eq
  · cases eq

/-- The isolated original large family remains a genuine parametricity filling. -/
noncomputable def familyWitness : FillingWitness template (closedGraph d C)
    (IsolatedFamily.largeRightFamily d m n) :=
  (IsolatedFamily.largeWitness d C).congr
    (Serial.Association.iso (IsolatedFamily.largeLeftFamily d m n)
      (C.atDepth (d+2)) (privateCell (d+2))) (DeepIso.refl _)

end Hypernets.Copying.Parametricity.LargeBareSource
