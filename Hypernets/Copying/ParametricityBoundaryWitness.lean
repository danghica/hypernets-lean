import Hypernets.Copying.ParametricityTemplate
import Hypernets.Copying.CopyingInputWitness
import Hypernets.Copying.CopyingInputIsomorphism

/-! Reordering complete Figure 20 families is justified by an actual common
input-permutation context. The private contraction tree is reindexed with
the recorded output action; no closure axiom is added to parametricity. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BoundaryWitness
open Graph

/-- Every bijection of a homogeneous term interface is a typed permutation. -/
def termOrder {m : Nat}
    (p : Bijection (Fin (List.replicate m Wire.term).length)
      (Fin (List.replicate m Wire.term).length)) :
    TypedPermutation (List.replicate m Wire.term) where
  bijection := p
  typed i := by
    change (List.replicate m Wire.term)[(p.toFun i).val] =
      (List.replicate m Wire.term)[i.val]
    simp only [List.getElem_replicate]

variable {d m n : Nat}
    {L : Hypernet (d+2) (List.replicate (m+n) .term) (List.replicate (m+n) .term)}
    {R : Hypernet (d+2) (List.replicate (m+n) .term) []}
    (f : BoundaryIso L (leftFamily d m n))
    (g : BoundaryIso R (rightFamily d m n))
    (C : ContractionTree .term (m+n))

/-- Reindex every input of the original tree with the exact private-output
action of the family isomorphism, retaining all primitive tree edges. -/
noncomputable def tree := CopyingInputPermutation.reordered C (termOrder f.outputs)

/-- The tree boundary action agrees with every shared private wire. -/
noncomputable def treeIso : BoundaryIso (C.atDepth (d+2)) ((tree f C).atDepth (d+2)) :=
  (CopyingInputPermutation.iso (C.atDepth (d+2)) (termOrder f.outputs)).trans
    (BoundaryIso.ofDeepIso (CopyingInputPermutation.reorderedIso C (termOrder f.outputs) (d+2)))

theorem compatible : BoundarySerial.Compatible f (treeIso f C) := by
  intro i
  rfl

/-- Whole private-cell assembly carries precisely the external input action
of the complete family, and fixes its empty output interface. -/
noncomputable def leftIso :
    BoundaryIso (Serial.net (Serial.net L (C.atDepth (d+2))) (privateCell (d+2)))
      (left d (tree f C)) :=
  BoundarySerial.iso (BoundarySerial.iso f (treeIso f C) (compatible f C))
    (BoundaryIso.refl (privateCell (d+2))) (by intro i; rfl)

theorem leftIso_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (leftIso f C).inputs.toFun i = f.inputs.toFun i := rfl

/-- The original literal parametricity pair, placed in a genuine common
permutation context, certifies arbitrary independently represented families
whose external input actions agree. -/
noncomputable def filling
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    FillingWitness template
      (Serial.net (Serial.net L (C.atDepth (d+2))) (privateCell (d+2))) R := by
  let p := termOrder f.inputs
  let l := CopyingInputPermutation.compensate (leftIso f C) p
    (leftIso_input f C) (fun i => Fin.elim0 i)
  let r := CopyingInputPermutation.compensate g p
    (fun i => (same i).symm) (fun i => Fin.elim0 i)
  exact ((FillingWitness.of_rel 0 (literal d (tree f C))).inputPermutation p.symm).congr l.symm r.symm

/-- A syntactically different presentation of the same homogeneous input
list needs only its proved interface equality, not a new semantic premise. -/
noncomputable def filling_reboundary {d m n : Nat} {I : List Wire}
    (hi : I = List.replicate (m+n) Wire.term)
    {L : Hypernet (d+2) I (List.replicate (m+n) .term)}
    {R : Hypernet (d+2) I []}
    (f : BoundaryIso L (leftFamily d m n))
    (g : BoundaryIso R (rightFamily d m n))
    (C : ContractionTree .term (m+n))
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    FillingWitness template
      (Serial.net (Serial.net L (C.atDepth (d+2))) (privateCell (d+2))) R := by
  cases hi
  exact filling f g C same

/-- Natural-number reassociation of the tree arity transports the complete
original assembly without changing its graph or its boundary coordinates. -/
noncomputable def filling_reboundary_tree {d m n N : Nat} {I : List Wire}
    (count : N = m+n) (hi : I = List.replicate (m+n) Wire.term)
    {L : Hypernet (d+2) I (List.replicate N .term)}
    {R : Hypernet (d+2) I []}
    (f : BoundaryIso L (leftFamily d m n))
    (g : BoundaryIso R (rightFamily d m n))
    (C : ContractionTree .term N)
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    FillingWitness template
      (Serial.net (Serial.net L (C.atDepth (d+2))) (privateCell (d+2))) R := by
  cases count
  exact filling_reboundary hi f g C same

end Hypernets.Copying.Parametricity.BoundaryWitness
