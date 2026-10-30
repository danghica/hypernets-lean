import Hypernets.Copying.SharingPayload

/-! A copyable payload's retained original owners are disjoint from every
same-sort sharing component, including original sharing holes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingPayload
open Graph RetainedFootprint
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (f : Opening.Occurrence G (C.expand L))

include cert trees copyable in
/-- A real payload edge never has a sharing-like original common owner. -/
theorem owner_notSharing (s : ShareSort) (e : G.Edge) :
    ¬ SharingLabel d s (C.edgeLabel (f.edges e).1) := by
  let avoid := avoids C cert trees copyable f
  let copy := RetainedFootprint.left C f.matchEmbedding cert avoid e
  have outer := (Copyable.outer_equiv d (f.label e)).mp (copyable.outer_labels e)
  intro sharing
  have impossible {p : Primitive} (old : C.edgeLabel (f.edges e).1 = primitiveLabel d p)
      (bad : ¬ Copyable.OuterLabel d (primitiveLabel d p)) : False := by
    have actual : (C.expand L).edgeLabel (f.edges e) = primitiveLabel d p := by
      change (L (f.edges e).1).edgeLabel (f.edges e).2 = _
      rw [copy.only (f.edges e).2]
      exact (copy.primitive _).mpr old
    exact bad (actual ▸ outer)
  rcases sharing with old | old | ⟨h,n,old,_,_⟩
  · apply impossible old; cases d <;> exact id
  · apply impossible old; cases d <;> exact id
  · apply impossible old; cases d <;> exact id

end Hypernets.Copying.SharingPayload
