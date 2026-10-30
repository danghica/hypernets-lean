import Hypernets.Copying.CopyingTemplateTwoSidedResidual
import Hypernets.Copying.CombinedPadding

/-! Equal ordered interfaces transport the actual copying residual and every
resume coordinate. No permutation or new relation closure is introduced. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph

private def boundaryRefl {d I O} (G : Hypernet d I O) : DeepIso G (G.reboundary rfl rfl) := {
  vertices := Bijection.refl _, edges := Bijection.refl _
  internal_label := fun _ => rfl
  edge_label := fun e => labelEquiv_refl d (G.edgeLabel e)
  source := by intro e; simp [Net.reboundary,Bijection.refl]
  target := by intro e; simp [Net.reboundary,Bijection.refl] }

noncomputable def Residual.reboundary {d I O J K} {G H : Hypernet d I O} {v w}
    (p : Residual G v H w) (hi : I = J) (ho : O = K) :
    Residual (G.reboundary hi ho) (Port.cast hi ho v)
      (H.reboundary hi ho) (Port.cast hi ho w) := by
  cases hi; cases ho
  simpa only [boundaryRefl,Bijection.refl,Port.map_id_fun,id_eq,Port.cast_refl] using
    p.congr (boundaryRefl G) (boundaryRefl H)

noncomputable def TwoSidedResidual.reboundary {d I O J K} {G H : Hypernet d I O} {v w}
    (p : TwoSidedResidual G v H w) (hi : I = J) (ho : O = K) :
    TwoSidedResidual (G.reboundary hi ho) (Port.cast hi ho v)
      (H.reboundary hi ho) (Port.cast hi ho w) := by
  cases hi; cases ho
  simpa only [boundaryRefl,Bijection.refl,Port.map_id_fun,id_eq,Port.cast_refl] using
    p.congr (boundaryRefl G) (boundaryRefl H)

/-- Cancel explicit interface equality transports on the actual graph. -/
theorem reboundary_cancel {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K) :
    (G.reboundary hi ho).reboundary hi.symm ho.symm = G := by
  cases hi; cases ho
  simp only [Net.reboundary_refl]

end Hypernets.Copying.CopyingTemplate
