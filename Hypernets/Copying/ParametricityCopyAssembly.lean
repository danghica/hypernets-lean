import Hypernets.Copying.ParametricityCopyContext
import Hypernets.Copying.ContractionTreeGraftSerial
import Hypernets.Copying.ContractionTreeGraftCongruence
import Hypernets.Copying.CopyingInputIsomorphism

/-! The exact residual-input context commutes with arbitrary serial
continuations. The explicit input action is preserved, not quotiented away. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph

noncomputable def serial {d I J O} (A : Hypernet d I J) (B : Hypernet d J O)
    (p : TypedPermutation I) :
    DeepIso (net (Serial.net A B) p) (Serial.net (net A p) B) := by
  let f := BoundarySerial.iso (iso A p) (BoundaryIso.refl B) (by intro i; rfl)
  let g := (iso (Serial.net A B) p).symm.trans f
  apply g.toDeepIso
  · intro i
    apply Port.input.inj (Internal := (Serial.net (net A p) B).Internal) (outputs := O.length)
    dsimp only [BoundaryIso.inputs]
    rw [← g.map_input]
    change f.ports.toFun (.input (p.bijection.invFun i)) = .input i
    have eq := BoundarySerial.iso_input (iso A p) (BoundaryIso.refl B) (by intro j; rfl)
      (p.bijection.invFun i)
    change f.ports.toFun (.input (p.bijection.invFun i)) = .input (p.bijection.toFun (p.bijection.invFun i)) at eq
    simpa only [p.bijection.right_inv] using eq
  · intro i
    apply Port.output.inj (Internal := (Serial.net (net A p) B).Internal) (inputs := I.length)
    dsimp only [BoundaryIso.outputs]
    rw [← g.map_output]
    change f.ports.toFun (.output i) = .output i
    exact BoundarySerial.iso_output (iso A p) (BoundaryIso.refl B) (by intro j; rfl) i

end Hypernets.Copying.CopyingInputPermutation

namespace Hypernets.Copying.Parametricity.CopyContext
open Graph
variable {d a b : Nat} {I O : List Wire}
    (P : Hypernet d (List.replicate a .term) [.term])

noncomputable def congr {G H : Hypernet d (List.replicate ((b+1)+1) .term) O}
    (f : DeepIso G H) : DeepIso (net P G) (net P H) :=
  CopyingInputPermutation.congr
    (ContractionTree.Graft.congr (s := .term) (b := b+1) (DeepIso.refl P) f (1 : Fin (b+1+1))) (rotation a b)

noncomputable def serial (G : Hypernet d (List.replicate ((b+1)+1) .term) I)
    (H : Hypernet d I O) : DeepIso (net P (Serial.net G H)) (Serial.net (net P G) H) :=
  (CopyingInputPermutation.congr
    (ContractionTree.Graft.SerialRight.iso (s := .term) (b := b+1) P G H 1) (rotation a b)).trans
      (CopyingInputPermutation.serial _ H (rotation a b))

end Hypernets.Copying.Parametricity.CopyContext
