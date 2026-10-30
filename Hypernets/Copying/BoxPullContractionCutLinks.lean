import Hypernets.Copying.OccurrenceAcrossCut
import Hypernets.Copying.BoxPullWeakeningCopyInjection

/-! Ordered attachment equations for the actual complement of a complete
occurrence, used to reassemble copying after a sharing-row interchange. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O J K L M P Q} {A : Hypernet d J K} {B : Hypernet d L M}
    {D : Hypernet d P Q} {G : Hypernet d I O} (f : Occurrence A G)
    (N : Hypernet d J K)

/-- The literal inserted replacement, with precisely the cut's old boundary. -/
noncomputable def replacement : Occurrence N (CompleteMatchCut.replaceWith f.matchEmbedding f.label N) :=
  (BoxPullWeakening.RetainedCopy.targetCast (Occurrence.ofIso (DeepIso.refl N))
    (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
    (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm).comp
      (Occurrence.plug (CompleteMatchCut.net f.matchEmbedding f.label) none _)

/-- A retained component's old attachment to a selected input remains exactly
attached to that same ordered input of the inserted replacement. -/
theorem acrossCut_replacement_input (g : Occurrence B G)
    (disjoint : ∀ a b, f.edges a ≠ g.edges b) (v : B.Vertex) (i : Fin J.length)
    (link : g.ports v = f.ports (.input i)) :
    (f.acrossCut g disjoint N).ports v = (f.replacement N).ports (.input i) := by
  let C := CompleteMatchCut.net f.matchEmbedding f.label
  let R := N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
    (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm
  change Net.Replacement.host C none R (cutPort f g disjoint v) =
    Net.Replacement.host C none R ((CompleteMatchCut.net f.matchEmbedding f.label).sourcePort none
      (Fin.cast (congrArg List.length (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm) i))
  rw [CompleteMatchCut.hole_sourcePort]
  apply congrArg (Net.Replacement.host C none R)
  apply CompleteMatchCut.embed_injective
  exact (CompleteMatchCut.embed_project _ _ _).trans
    (link.trans (CompleteMatchCut.embed_input f.matchEmbedding i).symm)

/-- The corresponding ordered output attachment survives the same cut. -/
theorem acrossCut_replacement_output (g : Occurrence B G)
    (disjoint : ∀ a b, f.edges a ≠ g.edges b) (v : B.Vertex) (i : Fin K.length)
    (link : g.ports v = f.ports (.output i)) :
    (f.acrossCut g disjoint N).ports v = (f.replacement N).ports (.output i) := by
  let C := CompleteMatchCut.net f.matchEmbedding f.label
  let R := N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
    (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm
  change Net.Replacement.host C none R (cutPort f g disjoint v) =
    Net.Replacement.host C none R ((CompleteMatchCut.net f.matchEmbedding f.label).targetPort none
      (Fin.cast (congrArg List.length (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm) i))
  rw [CompleteMatchCut.hole_targetPort]
  apply congrArg (Net.Replacement.host C none R)
  apply CompleteMatchCut.embed_injective
  exact (CompleteMatchCut.embed_project _ _ _).trans
    (link.trans (CompleteMatchCut.embed_output f.matchEmbedding i).symm)

/-- Two retained components preserve every old common vertex. -/
theorem acrossCut_link (g : Occurrence B G) (j : Occurrence D G)
    (dg : ∀ a b, f.edges a ≠ g.edges b) (dj : ∀ a b, f.edges a ≠ j.edges b)
    (v : B.Vertex) (w : D.Vertex) (link : g.ports v = j.ports w) :
    (f.acrossCut g dg N).ports v = (f.acrossCut j dj N).ports w := by
  let C := CompleteMatchCut.net f.matchEmbedding f.label
  let R := N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
    (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm
  change Net.Replacement.host C none R (cutPort f g dg v) =
    Net.Replacement.host C none R (cutPort f j dj w)
  apply congrArg (Net.Replacement.host C none R)
  apply CompleteMatchCut.embed_injective
  exact (CompleteMatchCut.embed_project _ _ _).trans
    (link.trans (CompleteMatchCut.embed_project _ _ _).symm)

end Hypernets.Copying.Opening.Occurrence
