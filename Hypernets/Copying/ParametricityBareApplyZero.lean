import Hypernets.Copying.ParametricityBareApplyBoundary
import Hypernets.Copying.BoundarySafety
import Hypernets.Graph.ExpansionIso

/-! The selected-input construction at zero is exactly the previously used
canonical bare application, up to boundary-fixing recursive representation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyFirst
open Graph

noncomputable def congr {d n} {G H : Hypernet d (List.replicate (n+1) .term) []}
    (f : DeepIso G H) : DeepIso (net G) (net H) := by
  apply Net.ExpansionIso.iso
  intro e
  cases d <;> cases e
  all_goals first | exact DeepIso.refl _ | exact f

end Hypernets.Copying.Parametricity.BareApplyFirst

namespace Hypernets.Copying.Parametricity.BareApplyAt
open Graph
variable {n : Nat}

theorem order_zero_identity (i : Fin (List.replicate (n+1) Wire.term).length) :
    (order (0 : Fin (n+1))).bijection.toFun i = i := by
  apply Fin.ext
  dsimp only [order,FamilyLiteral.front]
  split <;> (try split) <;> simp_all <;> omega

theorem order_zero_inverse (i : Fin (List.replicate (n+1) Wire.term).length) :
    (order (0 : Fin (n+1))).bijection.invFun i = i := by
  have h := (order (0 : Fin (n+1))).bijection.right_inv i
  rw [order_zero_identity] at h
  exact h

noncomputable def zeroIso {d} (G : Hypernet d (List.replicate (n+1) .term) []) :
    DeepIso (BareApplyFirst.net G) (net G 0) :=
  BareApplyFirst.congr ((CopyingInputPermutation.iso G (order 0).symm).toDeepIso
    order_zero_inverse (fun i => Fin.elim0 i))

end Hypernets.Copying.Parametricity.BareApplyAt
