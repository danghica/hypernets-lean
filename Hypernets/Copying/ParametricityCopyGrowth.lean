import Hypernets.Copying.ParametricityCopyDistributors
import Hypernets.Copying.ParametricityTensorGraft
import Hypernets.Copying.ParametricitySerialAssociation
import Hypernets.Copying.ParametricityGraphs
import Hypernets.Copying.ContractionTreeGraftCongruence
import Hypernets.Copying.ContractionTreeGraftSerial

/-! Duplication increases the actual Figure20 abstraction family and grafts
the complete canonical term D1,2 into its selected private-sharing input.
The private cell and its canonical atom distributor remain literally present. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyGrowth
open Graph
variable {d n : Nat}
    (H : Hypernet d [.term] [.term])
    (R : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (C : ContractionTree .term (n+1))

/-- Two copies replace exactly the selected first private-variable use.
The original old tree is retained as the whole downstream component. -/
def tree : ContractionTree .term (2+n) := (ContractionTree.canonical .term 2).graftInput C 0

/-- The old private continuation has only its equal list presentation exposed. -/
def tail : Hypernet d (.term :: List.replicate n .term) [] :=
  (Serial.net (C.atDepth d) (privateCell d)).reboundary (by simp [List.replicate_succ,ShareSort.wire]) rfl

/-- Both selected abstractions precede the untouched original family. -/
def doubled : Hypernet d ([.term,.term] ++ List.replicate n .term) (List.replicate (2+n) .term) :=
  (Net.Tensor.net (Net.Tensor.net H H) R).reboundary rfl (by rw [← List.replicate_append_replicate];rfl)

def before : Hypernet d ([.term,.term] ++ List.replicate n .term) [] :=
  Serial.net (Net.Tensor.net (CopyingMerge.net (a := 1) (b := 1) (k := 1) (h := 0) H H) R) (tail C)

def after : Hypernet d ([.term,.term] ++ List.replicate n .term) [] :=
  Serial.net (Serial.net (doubled H R) ((tree C).atDepth d)) (privateCell d)

noncomputable def tailIso : DeepIso (TensorGraft.tail (tail (d := d) C))
    (Serial.net (C.atDepth d) (privateCell d)) := by
  simp only [TensorGraft.tail,tail,Net.reboundary_refl]
  exact DeepIso.refl _

/-- Exact graph normalization, not merely a sharing law: the full actual
copying distributor becomes part of the original private contraction tree. -/
noncomputable def iso : DeepIso (before H R C) (after H R C) := by
  let X := Net.Tensor.net H H
  let D := CanonicalTree.atDepth .term 2 d
  have first : DeepIso (before H R C) (TensorGraft.source X D R (tail C)) :=
    Serial.congr (BoxPermutation.tensor_congr (CopyDistributors.privateMerge H).symm (DeepIso.refl R))
      (DeepIso.refl (tail C))
  have move := (TensorGraft.iso X D R (tail C)).symm
  have continuation : DeepIso
      (ContractionTree.Graft.net (s := .term) D (TensorGraft.tail (tail C)) 0)
      (Serial.net ((tree C).atDepth d) (privateCell d)) :=
    (ContractionTree.Graft.congr (DeepIso.refl D) (tailIso C) (0 : Fin (n+1))).trans
      ((ContractionTree.Graft.SerialRight.iso (s := .term) D (C.atDepth d) (privateCell d) 0).trans
        (Serial.congr ((ContractionTree.graftInput_iso (ContractionTree.canonical .term 2) C 0 d).symm)
          (DeepIso.refl (privateCell d))))
  exact first.trans (move.trans ((Serial.congr (DeepIso.refl _) continuation).trans
    (Serial.Association.iso (doubled H R) ((tree C).atDepth d) (privateCell d)).symm))

/-- The right-hand family has no private outputs. Removing only the empty
resource carriers leaves the two unchanged selected abstractions and rest. -/
noncomputable def closedIso {J K} (H : Hypernet d [.term] []) (R : Hypernet d J K) :
    DeepIso (Net.Tensor.net (CopyingMerge.net (a := 1) (b := 1) (k := 0) (h := 0) H H) R)
      (Net.Tensor.net (Net.Tensor.net H H) R) :=
  BoxPermutation.tensor_congr (CopyDistributors.closedMerge H).symm (DeepIso.refl R)

end Hypernets.Copying.Parametricity.CopyGrowth
