import Hypernets.Copying.ParametricityBoundaryWitness

/-! Normalize an independently represented abstraction family while keeping
the exact supplied original private tree on the target side. The isolated
source tree is obtained by the inverse recorded private-output action. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateReindex
open Graph
variable {d m n : Nat}
    {L : Hypernet (d+2) (List.replicate (m+n) .term) (List.replicate (m+n) .term)}
    {R : Hypernet (d+2) (List.replicate (m+n) .term) []}
    (f : BoundaryIso L (leftFamily d m n))
    (g : BoundaryIso R (rightFamily d m n))
    (C : ContractionTree .term (m+n))

/-- Pull back the actual original private tree along the inverse output
permutation; its full primitive tree and every original carrier are retained. -/
noncomputable def tree : ContractionTree .term (m+n) :=
  CopyingInputPermutation.reordered C (BoundaryWitness.termOrder f.outputs).symm

/-- The pullback tree maps back to the exact supplied tree, with input action
equal to the family's private-output action and its sole output fixed. -/
noncomputable def treeIso : BoundaryIso ((tree f C).atDepth (d+2)) (C.atDepth (d+2)) :=
  (BoundaryIso.ofDeepIso (CopyingInputPermutation.reorderedIso C
    (BoundaryWitness.termOrder f.outputs).symm (d+2))).symm.trans
    (CopyingInputPermutation.iso (C.atDepth (d+2)) (BoundaryWitness.termOrder f.outputs).symm).symm

/-- The exact two occurrences of each private family wire agree. -/
theorem compatible : BoundarySerial.Compatible f (treeIso f C) := by
  intro i
  rfl

/-- The whole isolated left graph maps to the original Figure20 left graph
with the exact originally supplied tree and literal private cell. -/
noncomputable def leftIso :
    BoundaryIso (Serial.net (Serial.net L ((tree f C).atDepth (d+2))) (privateCell (d+2)))
      (left d C) :=
  BoundarySerial.iso (BoundarySerial.iso f (treeIso f C) (compatible f C))
    (BoundaryIso.refl (privateCell (d+2))) (by intro i; rfl)

/-- Closing the private store does not change the recorded external action. -/
theorem leftIso_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftIso f C).inputs.toFun i = f.inputs.toFun i := rfl

/-- Cancel the common input action to obtain a boundary-fixing isomorphism
with the original left graph in an explicit common permutation context. -/
noncomputable def leftCompensated : DeepIso
    (Serial.net (Serial.net L ((tree f C).atDepth (d+2))) (privateCell (d+2)))
    (CopyingInputPermutation.net (left d C) (BoundaryWitness.termOrder f.inputs).symm) :=
  CopyingInputPermutation.compensate (leftIso f C) (BoundaryWitness.termOrder f.inputs)
    (leftIso_input f C) (fun i => Fin.elim0 i)

/-- The right side uses precisely the same common permutation context. -/
noncomputable def rightCompensated
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) : DeepIso R
    (CopyingInputPermutation.net (right d m n) (BoundaryWitness.termOrder f.inputs).symm) :=
  CopyingInputPermutation.compensate g (BoundaryWitness.termOrder f.inputs)
    (fun i => (same i).symm) (fun i => Fin.elim0 i)

/-- The resulting whole-graph pair is an actual original-template filling
of the exact supplied original pair, with no semantic closure assumption. -/
noncomputable def filling (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    FillingWitness template
      (Serial.net (Serial.net L ((tree f C).atDepth (d+2))) (privateCell (d+2))) R :=
  ((FillingWitness.of_rel 0 (literal d C)).inputPermutation
    (BoundaryWitness.termOrder f.inputs).symm).congr
      (leftCompensated f C).symm (rightCompensated f g same).symm

end Hypernets.Copying.Parametricity.PrivateReindex
