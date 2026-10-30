import Hypernets.Copying.ParametricityPrivateCorrection
import Hypernets.Copying.SharingExecution

/-! The two untouched atom weakenings in the private-cell complement attach
literally to the reconstructed read spine. Closing those inputs produces a
real one-input atom tree; the remaining private instance is not discarded. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateRead.AtomResidual
open Graph Opening
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

abbrev spine := ContractionSpine.tree .atom 2 orientation
abbrev localTree := ReadTail.Normal.residualTree spine

noncomputable def inserted : Occurrence (ReadTail.Normal.net spine d) (corrected T d) :=
  (tailOccurrence T d).replacement _

noncomputable def localCell : Occurrence (ReadTail.Normal.retainedCell spine d) (corrected T d) :=
  ((BoxPullWeakening.RetainedCopy.targetCast
    (Occurrence.ParallelJoin.component
      (Net.Tensor.family (ReadTail.numeral d) (ReadTail.Normal.retainedCell spine d))
      (Net.Tensor.boundary _ _ _ _) _ true)
    (by simp [Dereference.inputs]) (by simp [environmentInterface])).comp (inserted T d))

noncomputable def tree : Occurrence (localTree.atDepth d) (corrected T d) :=
  (BoxPullWeakening.ReverseComponents.serialLeft _ _).comp (localCell T d)

noncomputable def oldWeak (b : Bool) : Occurrence
    ((ContractionTree.canonical .atom 0).atDepth d) (ready T d) :=
  (Occurrence.ofIso ((ReadTail.Normal.atomWeakCopy d).iso
    (Occurrence.primitiveCopy d (.weakening .atom)) (labelEquiv_refl _ _))).comp
    (Occurrence.primitive (ready T d) (if b then oldShare T d 0 else newShare T d 0)
      (by cases b <;> cases d <;> rfl))

theorem weak_disjoint (b : Bool) : ∀ e j,
    (tailOccurrence T d).edges e ≠ (oldWeak T d b).edges j := by
  intro e j eq
  have weak := (oldWeak T d b).matchEmbedding.primitive j (.weakening .atom) (by rw [(ReadTail.Normal.atomWeakCopy d).only j]; exact (ReadTail.Normal.atomWeakCopy d).edge_label)
  have labels : ∀ c, (ReadTail.before spine d).edgeLabel c ≠ primitiveLabel d (.weakening .atom) := by
    cases d <;> rintro ⟨b,c⟩ <;> cases b
    all_goals first
      | (rcases c with ⟨e,c⟩; cases e <;> intro eq <;> cases eq)
      | (intro eq; cases eq)
  exact labels e ((Search.primitive_equiv ((tailOccurrence T d).label e) _).mpr
    ((congrArg (ready T d).edgeLabel eq).trans weak))

noncomputable def weak (b : Bool) : Occurrence
    ((ContractionTree.canonical .atom 0).atDepth d) (corrected T d) :=
  (tailOccurrence T d).acrossCut (oldWeak T d b) (weak_disjoint T d b) _

theorem oldWeak_link (b : Bool) :
    (oldWeak T d b).ports (.output 0) =
      (tailOccurrence T d).ports (.input ⟨if b then 3 else 2,by cases b <;> decide⟩) := by
  cases d <;> cases b <;> rfl

theorem tree_input (i : Fin 3) : (tree T d).ports (.input i) =
    (inserted T d).ports (.input ⟨i.val+1,by have := i.isLt; simp [Dereference.inputs]; omega⟩) := by
  have casesI : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases casesI with rfl | rfl | rfl <;> cases d <;> rfl

theorem weak_link (b : Bool) : (weak T d b).ports (.output 0) =
    (tree T d).ports (.input ⟨if b then 2 else 1,by cases b <;> decide⟩) := by
  rw [tree_input]
  cases b
  all_goals
    exact (tailOccurrence T d).acrossCut_replacement_input _ (oldWeak T d _) (weak_disjoint T d _)
      (.output 0) _ (oldWeak_link T d _)

theorem weak_tree_disjoint (b : Bool) : ∀ e c, (weak T d b).edges e ≠ (tree T d).edges c := by
  cases d <;> intro e c eq <;> cases eq

theorem weak_pair_disjoint : ∀ e c, (weak T d false).edges e ≠ (weak T d true).edges c := by
  apply (tailOccurrence T d).acrossCut_disjoint (oldWeak T d false) (oldWeak T d true)
    (weak_disjoint T d false) (weak_disjoint T d true)
  cases d <;> intro e c eq
  all_goals
    have h := congrArg Sigma.fst eq
    cases h

/-- Close the old cell's weakening attachment first, keeping both of the
other original atom inputs in order. -/
abbrev firstTree : ContractionTree .atom 2 :=
  ContractionTree.graftInput (ContractionTree.canonical .atom 0) localTree 2

noncomputable def first : Occurrence (firstTree.atDepth d) (corrected T d) :=
  (Occurrence.ofIso (ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) localTree 2 d)).comp
    (ContractionTree.Graft.Join.occurrence (weak T d true) (tree T d) 2
      (weak_link T d true) (weak_tree_disjoint T d true))

theorem first_input (i : Fin 2) : (first T d).ports (.input i) =
    (tree T d).ports (.input ⟨i.val,by simp; omega⟩) := by
  change (ContractionTree.Graft.Join.occurrence (weak T d true) (tree T d) 2
    (weak_link T d true) (weak_tree_disjoint T d true)).ports (.input i) = _
  have port : ContractionTree.Graft.rightInsert ((ContractionTree.canonical .atom 0).atDepth d)
      (localTree.atDepth d) 2 (.input ⟨i.val,by simp; omega⟩) = (.input i : (ContractionTree.Graft.net ((ContractionTree.canonical .atom 0).atDepth d) (localTree.atDepth d) 2).Vertex) := by
    have casesI : i=0 ∨ i=1 := by omega
    rcases casesI with rfl | rfl <;> cases d <;> rfl
  rw [← port,ContractionTree.Graft.Join.right_port]

theorem weak_first_disjoint : ∀ e c, (weak T d false).edges e ≠ (first T d).edges c := by
  intro e c
  change (weak T d false).edges e ≠
    (ContractionTree.Graft.Join.occurrence (weak T d true) (tree T d) 2
      (weak_link T d true) (weak_tree_disjoint T d true)).edges
      ((ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) localTree 2 d).edges.toFun c)
  generalize (ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) localTree 2 d).edges.toFun c = x
  cases d <;> rcases x with ⟨b,x⟩ <;> cases b
  all_goals first | exact weak_pair_disjoint T _ e x | exact weak_tree_disjoint T _ false e x

/-- The complete residual private atom network is genuinely a one-input
contraction tree. It includes all three consumed-path contractions and all
three actual weakening leaves. -/
abbrev fullTree : ContractionTree .atom 1 :=
  ContractionTree.graftInput (ContractionTree.canonical .atom 0) firstTree 1

noncomputable def full : Occurrence (fullTree.atDepth d) (corrected T d) :=
  (Occurrence.ofIso (ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) firstTree 1 d)).comp
    (ContractionTree.Graft.Join.occurrence (weak T d false) (first T d) 1
      ((weak_link T d false).trans (first_input T d 1).symm) (weak_first_disjoint T d))

theorem full_input : (full T d).ports (.input ⟨0,by decide⟩) = (tree T d).ports (.input ⟨0,by decide⟩) := by
  change (ContractionTree.Graft.Join.occurrence (weak T d false) (first T d) 1
    ((weak_link T d false).trans (first_input T d 1).symm) (weak_first_disjoint T d)).ports (.input ⟨0,by decide⟩) = _
  have port : ContractionTree.Graft.rightInsert ((ContractionTree.canonical .atom 0).atDepth d)
      (firstTree.atDepth d) 1 (.input ⟨0,by decide⟩) = (.input ⟨0,by decide⟩ : (ContractionTree.Graft.net
        ((ContractionTree.canonical .atom 0).atDepth d) (firstTree.atDepth d) 1).Vertex) := by
    cases d <;> rfl
  rw [← port,ContractionTree.Graft.Join.right_port,first_input]

theorem first_output : (first T d).ports (.output 0) = (tree T d).ports (.output 0) := by
  change (ContractionTree.Graft.Join.occurrence (weak T d true) (tree T d) 2
    (weak_link T d true) (weak_tree_disjoint T d true)).ports (.output 0) = _
  rw [← ContractionTree.Graft.right_output ((ContractionTree.canonical .atom 0).atDepth d)
    (localTree.atDepth d) 2 0,ContractionTree.Graft.Join.right_port]

theorem full_output : (full T d).ports (.output 0) = (tree T d).ports (.output 0) := by
  change (ContractionTree.Graft.Join.occurrence (weak T d false) (first T d) 1
    ((weak_link T d false).trans (first_input T d 1).symm) (weak_first_disjoint T d)).ports (.output 0) = _
  rw [← ContractionTree.Graft.right_output ((ContractionTree.canonical .atom 0).atDepth d)
    (firstTree.atDepth d) 1 0,ContractionTree.Graft.Join.right_port,first_output]

/-- Replace the complete residual atom network by the literal original
single-use distributor, leaving its private instance and store attached. -/
noncomputable def normalized : Hypernet d (List.replicate (n+1) .term) [] :=
  CompleteMatchCut.replaceWith (full T d).matchEmbedding (full T d).label
    ((ContractionTree.canonical .atom 1).atDepth d)

noncomputable def witness : FillingWitness SharingTreeAlgebra.template
    (corrected T d) (normalized T d) :=
  CompleteMatchCut.filling (full T d).matchEmbedding (full T d).label
    (PrivateRead.correction T d).second.filling.focusFree.2
    (FillingWitness.of_rel 0 (SharingTreeAlgebra.literal fullTree (ContractionTree.canonical .atom 1) d))

noncomputable def pointed : BoxPullWeakening.PointedWitness SharingTreeAlgebra.template
    (corrected T d) (correctedPoint T d) (normalized T d) (.input ⟨0,by simp⟩) := by
  rw [corrected_input]
  exact .input (witness T d) ⟨0,by simp⟩

end Hypernets.Copying.Parametricity.PrivateRead.AtomResidual
