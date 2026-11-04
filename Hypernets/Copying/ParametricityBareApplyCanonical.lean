import Hypernets.Copying.ParametricityBareApplyZero
import Hypernets.Copying.BoundarySynchrony

/-! Direct transport of the checked canonical first-member diagrams to the
actual originally selected family member, with its exact external action. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyAt.Boundary
open Graph
variable {d n} {G H : Hypernet d (List.replicate (n+1) .term) []}
    (f : BoundaryIso G H)

noncomputable def canonical : BoundaryIso (BareApplyFirst.net G) (net H (image f 0)) :=
  (BoundaryIso.ofDeepIso (zeroIso G)).trans (iso f 0)

theorem canonical_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (canonical f).inputs.toFun i = action f 0 i := by
  unfold canonical
  rw [BoundaryIso.trans_inputs]
  exact iso_input f 0 i

theorem canonical_active : (canonical f).inputs.toFun ⟨0,by simp⟩ = ⟨0,by simp⟩ := by
  rw [canonical_input]
  rfl

theorem canonical_output (i : Fin [Wire.term].length) : (canonical f).outputs.toFun i = i := by
  unfold canonical
  rw [BoundaryIso.trans_outputs]
  exact iso_output f 0 i

theorem canonical_same_inputs {G' H' : Hypernet d (List.replicate (n+1) .term) []}
    (g : BoundaryIso G' H') (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    ∀ i, (canonical f).inputs.toFun i = (canonical g).inputs.toFun i := by
  intro i
  rw [canonical_input,canonical_input]
  simp only [action,image_congr f g same,same]

end Hypernets.Copying.Parametricity.BareApplyAt.Boundary
