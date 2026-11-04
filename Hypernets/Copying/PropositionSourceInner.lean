import Hypernets.Copying.PropositionSourceGeometry

/-! Normalize the actual lambda w.!x under f,x. Every sharing component is a
checked tree; BPerm fixes w, and BPullC/BPullW act only on free resources. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Hypernets.Copying.Proposition12_2.Source
open Graph Structural

private instance : DecidableEq (weak 0).Internal := by graph_decide_eq
private instance : DecidableEq (unusedRow 0).Internal := by graph_decide_eq
private instance : DecidableEq (unusedRow 0).Edge := by graph_decide_eq
private instance : DecidableEq (usedRow 0).Internal := by graph_decide_eq
private instance : DecidableEq (usedRow 0).Edge := by graph_decide_eq

/-- Both weakenings and the contraction of the unused row are retained. -/
theorem unused_tree : SharingTreeGraph .term 0 (unusedRow 0) where
  labels := FiniteGraphCertificate.all (unusedRow 0).finiteEdge _ (by
    intro e member
    change e ∈ [(unusedRow 0).finiteEdge.elements[0],(unusedRow 0).finiteEdge.elements[1],(unusedRow 0).finiteEdge.elements[2]] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl)
  acyclic path := FiniteGraphCertificate.path_nodup _
    (FiniteGraphCertificate.table (unusedRow 0).finiteEdge.elements [0,0,1] 0) (by decide) path

/-- The variable row followed by the unary row is a genuine one-input tree. -/
theorem used_tree : SharingTreeGraph .term 1 (usedRow 0) where
  labels := FiniteGraphCertificate.all (usedRow 0).finiteEdge _ (by
    intro e member
    change e ∈ [(usedRow 0).finiteEdge.elements[0],(usedRow 0).finiteEdge.elements[1],(usedRow 0).finiteEdge.elements[2],(usedRow 0).finiteEdge.elements[3]] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl)
  acyclic path := FiniteGraphCertificate.path_nodup _
    (FiniteGraphCertificate.table (usedRow 0).finiteEdge.elements [0,1,0,2] 0) (by decide) path

noncomputable def unusedCalculation : Calculation (unusedRow 0) (weak 0) :=
  .sharing (.of_rel 0 (SharingTreeAlgebra.graphs unused_tree
    (show SharingTreeGraph .term 0 (weak 0) from {
      labels := fun _ => .inl rfl
      acyclic := fun path => FiniteGraphCertificate.path_nodup _ (fun _ => 0) (by decide) path })))
noncomputable def usedCalculation : Calculation (usedRow 0) (use 0) :=
  .sharing (.of_rel 0 (SharingTreeAlgebra.graphs used_tree
    ((ContractionTree.canonical .term 1).sharingTreeGraph 0)))

noncomputable def readCalculation : Calculation (Translation.term readTerm) readReduced :=
  (Calculation.iso ReadFactor.iso (Translation.term_focusFree _)).trans
    ((unusedCalculation.tensor unusedCalculation).tensor
      (usedCalculation.serialLeft (primitiveNet 0 (.operation (.unary .deref)))
        (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))))

/-- BPerm moves the unused free output past x while keeping the binder fixed;
BPullW then moves that actual weakening outside the box. -/
noncomputable def removeWeak {d} (G : Hypernet d [.term] (environmentInterface 2 0))
    (free : FocusFree G) : Calculation (lambdaPayload (beforeX G)) (outsideWeak G) := by
  have weakFree : FocusFree (BoxPullWeakening.body (n := 1) (k := 1) (h := 0) G .term) :=
    (BoxPullWeakening.body_allLabels (n := 1) (k := 1) (h := 0) _ G .term).mpr ⟨free,by intro m eq; cases eq⟩
  have perm : Calculation
      (box (bound := 1) (freeVariables := 2) (beforeX G))
      (InterfacePermutation.net (BoxPullWeakening.left (n := 1) (k := 1) (h := 0) G .term) swapPair.outer.symm) :=
    .permutation (.of_rel 0 ⟨.witness (DeepIso.refl _) (.permute _ swapPair) (DeepIso.refl _),fun _ => weakFree⟩)
  have pull : Calculation (BoxPullWeakening.left (n := 1) (k := 1) (h := 0) G .term)
      (BoxPullWeakening.right (n := 1) (k := 1) (h := 0) G .term) :=
    .pull (.of_rel 0 (BoxPullWeakening.literal (n := 1) (k := 1) (h := 0) G .term free))
  exact (perm.trans (pull.permuted swapPair.outer.symm)).serialLeft
    (primitiveNet (d+1) (.operation .lam))
    (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))

/-- Pull the contraction of the one-use row outside its original box. -/
noncomputable def pullContraction {d} (G : Hypernet d [.term] (environmentInterface 2 0))
    (free : FocusFree G) : Calculation (lambdaPayload (insideUse G)) (pullRight G) := by
  have weakFree : FocusFree (beforeX G) :=
    (BoxPullWeakening.body_allLabels (n := 1) (k := 1) (h := 0) _ G .term).mpr ⟨free,by intro m eq; cases eq⟩
  exact (Calculation.contraction (.of_rel 0
    (BoxPullContraction.literal (n := 1) (k := 0) (h := 0) .term (beforeX G) weakFree))).serialLeft
      (primitiveNet (d+1) (.operation .lam))
      (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))

/-- The read lambda has its original one-use x row moved outside the box. -/
noncomputable def smallUseCalculation : Calculation smallUsed
    (Serial.net (Parametricity.smallLeft 0) (use 1)) := by
  have free := (Parametricity.labels_closed (Parametricity.readBody_labels 0)).1
  have first := pullContraction (Parametricity.readBody 0) free
  have middle := (removeWeak (Parametricity.readBody 0) free).serialRight
    (primitiveNet 1 (.contraction .term))
    (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))
  exact first.trans ((Calculation.iso SmallPull.iso first.focusFree.2).trans
    (middle.trans (.iso SmallUse.iso middle.focusFree.2)))

/-- The original inner lambda is normalized with both outer distributor rows
still present, including the unused f row. -/
noncomputable def innerCalculation : Calculation
    (Translation.term (.lam readTerm : Term 2 0)) innerNormal := by
  have c := (readCalculation.trans (.iso ReadUnused.iso readCalculation.focusFree.2)).abstraction
  have bodyFree : FocusFree readUsed := by
    have both := (allLabels_iso_iff _ ReadUnused.iso).mp readCalculation.focusFree.2
    exact ((BoxPullWeakening.body_allLabels (n := 1) (k := 1) (h := 0) _ readUsed .term).mp both).1
  have d := (removeWeak readUsed bodyFree).serialRight
    (Translation.singleUse 1 2 0) (Translation.language_focusFree (Translation.singleUse_language _ _ _))
  have e := (smallUseCalculation.tensorLeft (weak 1)
    (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))).serialRight
      (Translation.singleUse 1 2 0) (Translation.language_focusFree (Translation.singleUse_language _ _ _))
  exact c.trans (d.trans ((Calculation.iso
    (Serial.congr UnusedOutside.iso (DeepIso.refl _)) d.focusFree.2).trans e))

end Hypernets.Copying.Proposition12_2.Source
