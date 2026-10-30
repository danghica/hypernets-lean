import Hypernets.Copying.SharingNonsharingFootprint
import Hypernets.Copying.RetainedFootprintNormalisation

/-! Fully primitive nonsharing footprints occur unchanged in the original
common context, preserving every actual port coordinate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingOverlap
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (closed : HoleFree (C.expand L)) {J K} {G : Hypernet d J K}
    (f : Occurrence G (C.expand L)) (nonsharing : Nonsharing G)
    (primitive : BoxPermutation.PrimitiveFootprint G)

/-- The concrete primitive footprint itself, with its original full labels,
embeds into the old common context rather than only into its expansion. -/
noncomputable def primitiveOccurrence : Occurrence G C :=
  let matching := RetainedFootprint.reflect C f.matchEmbedding cert (avoids C cert trees closed f nonsharing)
  matching.occurrence (fun e => by
    obtain ⟨p,label⟩ := primitive e
    rw [matching.primitive e p label,label]
    exact labelEquiv_refl _ _)

/-- Reflecting this footprint keeps its actual host coordinate exactly. -/
theorem primitiveOccurrence_host (v : G.Vertex) :
    Net.Expansion.host C L ((primitiveOccurrence C cert trees closed f nonsharing primitive).ports v) = f.ports v := by
  exact RetainedFootprint.host_port C f.matchEmbedding cert (avoids C cert trees closed f nonsharing) v

end Hypernets.Copying.SharingOverlap
