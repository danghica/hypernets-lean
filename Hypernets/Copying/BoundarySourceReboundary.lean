import Hypernets.Copying.BoundaryReboundary
import Hypernets.Copying.BoundarySynchrony

/-! Exact source interface casts for family boundary isomorphisms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryIso
open Graph

theorem interfaceEquality_inverse {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K)
    (v : (G.reboundary hi ho).Vertex) :
    (interfaceEquality G hi ho).ports.invFun v = Port.cast hi.symm ho.symm v := by
  apply (interfaceEquality G hi ho).ports.injective
  rw [Bijection.right_inv,interfaceEquality_port]
  cases hi; cases ho
  cases v <;> rfl

/-- Change only the source interface presentation; the full original target
family and its ordered coordinates remain literal. -/
noncomputable def reboundarySource {d I O J K U V} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) (hi : I = U) (ho : O = V) : BoundaryIso (G.reboundary hi ho) H :=
  (interfaceEquality G hi ho).symm.trans f

theorem reboundarySource_inputs {d I O J K U V} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) (hi : I = U) (ho : O = V) (i : Fin U.length) :
    (f.reboundarySource hi ho).inputs.toFun i =
      f.inputs.toFun (Fin.cast (congrArg List.length hi.symm) i) := by
  apply Port.input.inj (Internal := H.Internal) (outputs := K.length)
  change Port.input ((f.reboundarySource hi ho).inputMap i) = Port.input (f.inputMap _)
  rw [← map_input,← map_input]
  change f.ports.toFun ((interfaceEquality G hi ho).ports.invFun (.input i)) = _
  rw [interfaceEquality_inverse]
  rfl

theorem reboundarySource_outputs {d I O J K U V} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) (hi : I = U) (ho : O = V) (i : Fin V.length) :
    (f.reboundarySource hi ho).outputs.toFun i =
      f.outputs.toFun (Fin.cast (congrArg List.length ho.symm) i) := by
  apply Port.output.inj (Internal := H.Internal) (inputs := J.length)
  change Port.output ((f.reboundarySource hi ho).outputMap i) = Port.output (f.outputMap _)
  rw [← map_output,← map_output]
  change f.ports.toFun ((interfaceEquality G hi ho).ports.invFun (.output i)) = _
  rw [interfaceEquality_inverse]
  rfl

end Hypernets.Copying.BoundaryIso
