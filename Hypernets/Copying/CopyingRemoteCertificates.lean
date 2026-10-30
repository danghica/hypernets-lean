import Hypernets.Copying.CopyingRemoteContext
import Hypernets.Copying.RetainedFootprint
import Hypernets.Copying.TemplateInputSafety

/-! Every original sharing-prefix edge has a literal retained corolla on
both sides. These certificates follow from the actual template filling,
rather than an assumption that the matched footprint is retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteContext
open Graph Opening

/-- A primitive non-hole edge retains its exact label on both actual sides,
including interfaces and the absence of hidden additional edges. -/
noncomputable def primitiveCopies {T : PreTemplate} {d I O}
    (C : Hypernet d I O) {L R e} (cert : DeepFillingEdge T C L R e)
    {p : Primitive} (label : C.edgeLabel e = primitiveLabel d p)
    (notHole : ∀ h, p ≠ .hole h) :
    LabelCopy (L e) (primitiveLabel d p) × LabelCopy (R e) (primitiveLabel d p) := by
  let copies := Classical.choice (cert.retained_of_not_hole
    (fun h bad => notHole h (primitiveLabel_injective d (label.symm.trans bad))))
  exact ⟨⟨copies.1.edge,(copies.1.primitive p).mpr label,copies.1.source,copies.1.target,copies.1.only⟩,
    ⟨copies.2.edge,(copies.2.primitive p).mpr label,copies.2.source,copies.2.target,copies.2.only⟩⟩

/-- The actual complete prefix's primitive labels exclude shallow copying
holes, on every branch of its original tree. -/
noncomputable def treeCopies {T : PreTemplate} {d I O m}
    (C : Hypernet d I O) {L R} (cert : ∀ e, DeepFillingEdge T C L R e)
    (P : ContractionTree .term m) (f : Occurrence (P.atDepth d) C) (e : (P.atDepth d).Edge) :
    LabelCopy (L (f.edges e)) ((P.atDepth d).edgeLabel e) ×
      LabelCopy (R (f.edges e)) ((P.atDepth d).edgeLabel e) := by
  classical
  have labels := (P.sharingTreeGraph d).labels e
  by_cases weak : (P.atDepth d).edgeLabel e = primitiveLabel d (.weakening .term)
  · have original : C.edgeLabel (f.edges e) = primitiveLabel d (.weakening .term) :=
      f.matchEmbedding.primitive _ _ weak
    simpa only [weak] using primitiveCopies C (cert (f.edges e)) original (fun h bad => by cases bad)
  · have contraction := labels.resolve_left weak
    have original : C.edgeLabel (f.edges e) = primitiveLabel d (.contraction .term) :=
      f.matchEmbedding.primitive _ _ contraction
    simpa only [contraction] using primitiveCopies C (cert (f.edges e)) original (fun h bad => by cases bad)

/-- Equality transports the existing pair's ordered boundary and does not
add an assumption or closure constructor to the original copying relation. -/
theorem pair_reboundary {d I O J K} {G H : Hypernet d I O}
    (pair : Pair G H) (hi : I = J) (ho : O = K) :
    Pair (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using pair

end Hypernets.Copying.CopyingTemplate.RemoteContext
