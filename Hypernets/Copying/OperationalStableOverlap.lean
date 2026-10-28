import Hypernets.Copying.OperationalHeadOrigin

/-! Stable arguments cannot begin inside a shallow left operational filling.
The argument is flat and keeps the original stable-graph premises. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ForwardOverlap
open Graph Search.Expansion
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
include cert

/-- A stable graph's actual entire occurrence avoids shallow operational holes
when its input is attached at any original context coordinate. -/
theorem stable_avoids {J} {G : Hypernet d [.term] J} (stable : Stable G)
    (f : MatchEmbedding G (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f := by
  intro e h
  obtain ⟨p,label,passive⟩ := stable.labels e
  have head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) (f.edges e) p := by
    rw [← attached]
    exact f.head ⟨label,Stable.input_source stable.labels e⟩
  apply head_not_hole C cert head _ _ h
  · intro eq
    subst p
    cases kind <;> cases passive
  · intro name eq
    subst p
    exact passive

/-- Any stable primitive immediately after a retained original edge also has
an original non-hole owner. Target-origin reflection supplies its actual host
coordinate, without assuming injectivity of boundary attachments. -/
theorem stable_after_retained {a b : (C.expand L).Edge}
    (copy : Retained C L a.1) (adj : (C.expand L).Adjacent a b)
    (stable : StableLabel d ((C.expand L).edgeLabel b)) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨w,target,source⟩ := adj
  obtain ⟨v,eq⟩ := copy.target_origin target
  obtain ⟨p,label,passive⟩ := stable
  apply head_not_hole C cert ⟨label,eq ▸ source⟩
  · intro eq
    subst p
    cases kind <;> cases passive
  · intro name eq
    subst p
    exact passive

end Hypernets.Copying.OperationalTemplates.ForwardOverlap
