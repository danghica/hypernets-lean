import Hypernets.Copying.ParametricityPrivateResidualCover
import Hypernets.Copying.ParametricitySerialAssociation

/-! The private read's family-ready residual preserves its literal original
cell and complete weakened term tree. Only the proved sharing-tree equation
normalizes the three-contraction private atom network. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateRead
open Graph Opening
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

/-- One returned numeral is separated from the whole remaining private cell.
The selected term input is closed by the original residual-tree weakening. -/
def result : Hypernet d (List.replicate (n+1) .term) [] :=
  (Net.Tensor.net (ReadTail.numeral d)
    (Serial.net (CopyRule.residual T d) (privateCell d))).reboundary
      (by simp [List.replicate_succ]) rfl

noncomputable def cell_association : DeepIso (privateCell d)
    (Serial.net (primitiveNet d .instanceEdge)
      (Serial.net ((ContractionTree.canonical .atom 1).atDepth d) (ReadTail.Normal.cell d))) :=
  (Serial.Association.iso
    (Serial.net (primitiveNet d .instanceEdge) ((ContractionTree.canonical .atom 1).atDepth d))
    (primitiveNet d .store) (ReadTail.numeral d)).trans
      (Serial.Association.iso (primitiveNet d .instanceEdge)
        ((ContractionTree.canonical .atom 1).atDepth d) (ReadTail.Normal.cell d))

noncomputable def stored_association : DeepIso
    (Serial.net (ResidualNormal.reference T d)
      (Serial.net ((ContractionTree.canonical .atom 1).atDepth d) (ReadTail.Normal.cell d)))
    (Serial.net (CopyRule.residual T d) (privateCell d)) :=
  (Serial.Association.iso (CopyRule.residual T d) (primitiveNet d .instanceEdge)
    (Serial.net ((ContractionTree.canonical .atom 1).atDepth d) (ReadTail.Normal.cell d))).trans
      (Serial.congr (DeepIso.refl _) (cell_association d).symm)

/-- The only structural correction is a literal pair of finite atom trees.
Complete reconstruction and serial association recover the unchanged store
encoding, including its canonical D1,1 and numeral. -/
noncomputable def sharing_residual : FillingWitness SharingTreeAlgebra.template
    (corrected T d) (result T d) := by
  let tree := FillingWitness.of_rel 0
    (SharingTreeAlgebra.literal AtomResidual.fullTree (ContractionTree.canonical .atom 1) d)
  let cell := FillingWitness.refl (T := SharingTreeAlgebra.template) (ReadTail.Normal.cell d)
    (Serial.focusFree_net (by cases d <;> intro e m eq <;> cases eq)
      (by cases d <;> intro e m eq <;> cases eq))
  let reference := FillingWitness.refl (T := SharingTreeAlgebra.template) (ResidualNormal.reference T d)
    (Serial.focusFree_net (ContractionAlgebra.tree_focusFree (CopyRule.residualTree T) d)
      (by cases d <;> intro e m eq <;> cases eq))
  let numeral := FillingWitness.refl (T := SharingTreeAlgebra.template) (ReadTail.numeral d) (by cases d <;> intro e m eq <;> cases eq)
  let w := (numeral.tensor (reference.serial (tree.serial cell))).reboundary (J := List.replicate (n+1) .term) (K := [])
    (by simp [List.replicate_succ]) rfl
  exact w.congr (ResidualNormal.iso T d)
    (CopyRule.reboundaryIso (BoxPermutation.tensor_congr (DeepIso.refl _) (stored_association T d)) _ _)

noncomputable def sharing_pointed : BoxPullWeakening.PointedWitness SharingTreeAlgebra.template
    (corrected T d) (correctedPoint T d) (result T d) (.input ⟨0,by simp⟩) := by
  rw [corrected_input]
  exact .input (sharing_residual T d) ⟨0,by simp⟩

/-- The unchanged eight-step execution has a fully constructed residual
chain ending in an ordered returned value and the original private cell. -/
theorem residual_factorization :
    (Combined.machine d (List.replicate (n+1) .term) []).Steps 8
      ⟨before T d,(.search,.input ⟨0,by simp⟩)⟩ (after T d) ∧
    Nonempty (ReadCorrection (after T d).1 (after T d).2.2 (corrected T d) (correctedPoint T d)) ∧
    Nonempty (BoxPullWeakening.PointedWitness SharingTreeAlgebra.template
      (corrected T d) (correctedPoint T d) (result T d) (.input ⟨0,by simp⟩)) :=
  ⟨run T d,⟨correction T d⟩,⟨sharing_pointed T d⟩⟩

end Hypernets.Copying.Parametricity.PrivateRead
