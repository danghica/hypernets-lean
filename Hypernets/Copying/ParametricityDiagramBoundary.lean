import Hypernets.Copying.ParametricityInputResidual
import Hypernets.Copying.BoundarySafety

/-! Move a complete original opening/read/correction certificate through
different family-member presentations that have the same recorded input
permutation and fixed external outputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadDiagram
open Graph CopyingInputPermutation

private theorem symm_input_action {d I O} {G H : Hypernet d I O}
    (f : BoundaryIso G H) (p : TypedPermutation I)
    (inputAction : ∀ i, f.inputs.toFun i = p.bijection.toFun i) (i : Fin I.length) :
    f.symm.inputs.toFun i = p.symm.bijection.toFun i := by
  apply p.bijection.injective
  have h := f.inputs.right_inv i
  rw [inputAction] at h
  calc
    p.bijection.toFun (f.symm.inputs.toFun i) = i := h
    _ = p.bijection.toFun (p.symm.bijection.toFun i) := by
      symm
      exact p.bijection.right_inv i


private theorem symm_output_action {d I O} {G H : Hypernet d I O}
    (f : BoundaryIso G H) (outputAction : ∀ i, f.outputs.toFun i = i)
    (i : Fin O.length) : f.symm.outputs.toFun i = i := by
  apply f.outputs.injective
  have h := f.outputs.right_inv i
  change f.outputs.toFun (f.outputs.invFun i) = i at h
  calc
    f.outputs.toFun (f.symm.outputs.toFun i) = i := by simpa only [BoundaryIso.outputs] using h
    _ = f.outputs.toFun i := (outputAction i).symm

private theorem typed_symm_symm {I} (p : TypedPermutation I) : p.symm.symm = p := by
  cases p
  rfl

/-- A boundary isomorphism whose input action is `p` and whose output action
is fixed becomes an ordinary recursive isomorphism after the actual inverse
input-permutation context. The transformation preserves all intermediate
states and rewrite costs in a `ReadDiagram`. -/
noncomputable def synchronousBoundary {d I O} {G H G' H' : Hypernet (d+1) I O}
    {i : Fin I.length} {n : Nat}
    (q : ReadDiagram G (.input i) H (.input i) n)
    (f : BoundaryIso G G') (g : BoundaryIso H H')
    (p : TypedPermutation I)
    (leftInput : ∀ j, f.inputs.toFun j = p.bijection.toFun j)
    (rightInput : ∀ j, g.inputs.toFun j = p.bijection.toFun j)
    (leftOutput : ∀ j, f.outputs.toFun j = j)
    (rightOutput : ∀ j, g.outputs.toFun j = j) :
    ReadDiagram G' (.input (p.bijection.toFun i))
      H' (.input (p.bijection.toFun i)) n := by
  let leftIso : DeepIso (net G p) G' := by
    have h := (compensate f.symm p.symm (symm_input_action f p leftInput)
      (symm_output_action f leftOutput)).symm
    simpa only [typed_symm_symm] using h
  let rightIso : DeepIso (net H p) H' := by
    have h := (compensate g.symm p.symm (symm_input_action g p rightInput)
      (symm_output_action g rightOutput)).symm
    simpa only [typed_symm_symm] using h
  have moved := q.inputPermutation p
  have result := moved.congr leftIso rightIso
  simpa only [ReadDiagram.congr, ReadDiagram.inputPermutation,
    CopyingInputPermutation.ports, Bijection.toFun, Port.map, Function.comp_apply] using result

end Hypernets.Copying.Parametricity.ReadDiagram
