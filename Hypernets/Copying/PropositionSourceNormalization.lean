import Hypernets.Copying.PropositionSourceOuterGeometry
import Hypernets.Copying.PropositionParametricityInstance

/-! Complete source-body normalization through the original templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Hypernets.Copying.Proposition12_2.Source
open Graph Structural

private instance : DecidableEq (callbackTree).Internal := by graph_decide_eq
private instance : DecidableEq (callbackTree).Edge := by graph_decide_eq

/-- Exhaustive primitive labels and strictly increasing edge ranks certify this actual tree. -/
theorem callback_tree : SharingTreeGraph .term 1 (callbackTree) where
  labels := FiniteGraphCertificate.all (callbackTree).finiteEdge _ (by
    intro e member
    change e ∈ [(callbackTree).finiteEdge.elements[0],(callbackTree).finiteEdge.elements[1],(callbackTree).finiteEdge.elements[2],(callbackTree).finiteEdge.elements[3],(callbackTree).finiteEdge.elements[4],(callbackTree).finiteEdge.elements[5],(callbackTree).finiteEdge.elements[6],(callbackTree).finiteEdge.elements[7],(callbackTree).finiteEdge.elements[8],(callbackTree).finiteEdge.elements[9],(callbackTree).finiteEdge.elements[10],(callbackTree).finiteEdge.elements[11]] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl)
  acyclic path := FiniteGraphCertificate.path_nodup _
    (FiniteGraphCertificate.table (callbackTree).finiteEdge.elements [0,0,1,0,1,0,0,3,2,0,5,4] 0) (by decide) path

private instance : DecidableEq (privateTree).Internal := by graph_decide_eq
private instance : DecidableEq (privateTree).Edge := by graph_decide_eq

/-- Exhaustive primitive labels and strictly increasing edge ranks certify this actual tree. -/
theorem private_tree : SharingTreeGraph .term 1 (privateTree) where
  labels := FiniteGraphCertificate.all (privateTree).finiteEdge _ (by
    intro e member
    change e ∈ [(privateTree).finiteEdge.elements[0],(privateTree).finiteEdge.elements[1],(privateTree).finiteEdge.elements[2],(privateTree).finiteEdge.elements[3],(privateTree).finiteEdge.elements[4],(privateTree).finiteEdge.elements[5],(privateTree).finiteEdge.elements[6],(privateTree).finiteEdge.elements[7],(privateTree).finiteEdge.elements[8],(privateTree).finiteEdge.elements[9],(privateTree).finiteEdge.elements[10],(privateTree).finiteEdge.elements[11]] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl)
  acyclic path := FiniteGraphCertificate.path_nodup _
    (FiniteGraphCertificate.table (privateTree).finiteEdge.elements [0,1,0,2,0,0,0,2,1,0,4,3] 0) (by decide) path

private instance : DecidableEq (usedRow 2).Internal := by graph_decide_eq
private instance : DecidableEq (usedRow 2).Edge := by graph_decide_eq

/-- Exhaustive primitive labels and strictly increasing edge ranks certify this actual tree. -/
theorem outer_tree : SharingTreeGraph .term 1 (usedRow 2) where
  labels := FiniteGraphCertificate.all (usedRow 2).finiteEdge _ (by
    intro e member
    change e ∈ [(usedRow 2).finiteEdge.elements[0],(usedRow 2).finiteEdge.elements[1],(usedRow 2).finiteEdge.elements[2],(usedRow 2).finiteEdge.elements[3]] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl)
  acyclic path := FiniteGraphCertificate.path_nodup _
    (FiniteGraphCertificate.table (usedRow 2).finiteEdge.elements [0,1,0,2] 0) (by decide) path

noncomputable def callbackCalculation : Calculation callbackTree (use 1) :=
  .sharing (.of_rel 0 (SharingTreeAlgebra.graphs callback_tree
    ((ContractionTree.canonical .term 1).sharingTreeGraph 1)))
noncomputable def privateCalculation : Calculation privateTree (use 1) :=
  .sharing (.of_rel 0 (SharingTreeAlgebra.graphs private_tree
    ((ContractionTree.canonical .term 1).sharingTreeGraph 1)))
noncomputable def outerCalculation : Calculation (usedRow 2) (use 2) :=
  .sharing (.of_rel 0 (SharingTreeAlgebra.graphs outer_tree
    ((ContractionTree.canonical .term 1).sharingTreeGraph 2)))

/-- The unchanged translated application retains its argument and distributor. -/
noncomputable def sequenceCalculation : Calculation (Translation.term sequenceTerm) sequenceNormal :=
  innerCalculation.application (.refl _
    ((Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_focusFree callbackTerm)))

/-- The two independent sharing trees are normalized while both application
heads, unit, and the complete read-lambda box remain unchanged. -/
noncomputable def sequenceSharing : Calculation sequenceNormal
    (insideUse (Parametricity.callReadBody 0)) := by
  have c := (((privateCalculation.serialLeft (Parametricity.smallLeft 0)
    (Parametricity.labels_closed (Parametricity.smallLeft_labels 0)).1).tensor
      ((callbackCalculation.tensorRight (primitiveNet 1 (.operation (.const .unit)))
        (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))).serialLeft
          (primitiveNet 1 (.operation .app))
          (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq)))).serialLeft
            (primitiveNet 1 (.operation .app))
            (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))).permuted Parametricity.boundFirst
  exact (Calculation.iso SequenceFactor.iso sequenceCalculation.focusFree.2).trans
    (c.trans (.iso SequenceUse.iso c.focusFree.2))

/-- Pull the remaining free x row through the large box; f stays bound. -/
noncomputable def largeUseCalculation : Calculation
    (lambdaPayload (insideUse (Parametricity.callReadBody 0)))
    (Serial.net (Parametricity.largeLeft 0) (use 2)) := by
  have free := (Parametricity.labels_closed (Parametricity.callReadBody_labels 0)).1
  have first := pullContraction (Parametricity.callReadBody 0) free
  have middle := (removeWeak (Parametricity.callReadBody 0) free).serialRight
    (primitiveNet 2 (.contraction .term))
    (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))
  exact first.trans ((Calculation.iso LargePull.iso first.focusFree.2).trans
    (middle.trans (.iso LargeUse.iso middle.focusFree.2)))

/-- The entire literal translated let body is normalized, preserving the
outer single-use row before replacing its complete sharing tree. -/
noncomputable def bodyCalculation : Calculation body
    (Serial.net (Parametricity.largeLeft 0) (use 2)) := by
  have a := (sequenceCalculation.trans sequenceSharing).abstraction
  have b := largeUseCalculation.serialRight (Translation.singleUse 2 1 0)
    (Translation.language_focusFree (Translation.singleUse_language _ _ _))
  have c := outerCalculation.serialLeft (Parametricity.largeLeft 0)
    (Parametricity.labels_closed (Parametricity.largeLeft_labels 0)).1
  exact a.trans (b.trans ((Calculation.iso AbstractionSuffix.iso b.focusFree.2).trans c))

/-- Padding preserves the normalized body including its complete single-use tree. -/
noncomputable def normalized_raise (d : Nat) : DeepIso
    (raise (d+2) (Serial.net (Parametricity.largeLeft d) (use (d+2))))
    (Serial.net (Parametricity.largeLeft (d+1)) (use (d+3))) :=
  (Padding.serial _ _).trans (Serial.congr (Parametricity.largeLeft_raise d) (DeepIso.refl _))

/-- The actual opened left graph reaches the concrete private parametricity
source; the instance, atom row, store and numeral remain in place. -/
noncomputable def openedCalculation : Calculation opened (ParametricInstance.privateClosure 1) := by
  have first : Calculation opened (Serial.net (raise 2 body) (Parametricity.privateCell 3)) :=
    .iso Opened.iso (by
      apply (allLabels_iso_iff _ Opened.iso).mpr
      exact Serial.allLabels_net _ ((allLabels_raise_iff _ _ _).mpr bodyCalculation.focusFree.1)
        (Parametricity.labels_closed (Parametricity.privateCell_labels 3)).1)
  have middle := bodyCalculation.raise.serialRight (Parametricity.privateCell 3)
    (Parametricity.labels_closed (Parametricity.privateCell_labels 3)).1
  exact first.trans (middle.trans (.iso (Serial.congr (normalized_raise 0) (DeepIso.refl _)) middle.focusFree.2))

end Hypernets.Copying.Proposition12_2.Source
