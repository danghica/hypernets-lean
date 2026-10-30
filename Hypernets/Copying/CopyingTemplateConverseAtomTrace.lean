import Hypernets.Copying.CopyingTemplateConverseHead
import Hypernets.Copying.EqualityTreeRematch
import Hypernets.Copying.TwoInputContractionSubtree

/-! Atom traces starting at an evaluated original instance cannot enter
shallow copying holes, whose entire input interface consists of term wires.
Unused side branches are deliberately outside this selected-path claim. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ConverseOverlap
open Graph Search.Expansion Opening
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (rightClosed : HoleFree (C.expand R))
include cert rightClosed

/-- An actual retained atom-trace predecessor gives a host coordinate for its
next edge, and typing excludes a term-input copying replacement there. -/
theorem atom_hop_not_hole {a b : (C.expand R).Edge}
    (retained : ∀ h, C.edgeLabel a.1 ≠ primitiveLabel d (.hole h))
    (hop : StoreTrace.Hop (C.expand R) a b) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨_,copy⟩ := (cert a.1).retained_of_not_hole retained
  obtain ⟨w,target,source⟩ := hop.2
  obtain ⟨q,eq⟩ := copy.target_origin target
  apply nonterm_source_not_hole C cert (eq ▸ source)
  · have typed : (C.expand R).vertexLabel w = .atom := by
      have mem := List.mem_map_of_mem (f := (C.expand R).vertexLabel) target
      dsimp only [Net.vertexLabel] at mem
      rw [(C.expand R).target_typed,StoreTrace.forward_output hop.1] at mem
      exact List.mem_singleton.mp mem
    rw [eq,typed]
    decide
  · intro h label
    have no := rightClosed b
    rw [label] at no
    cases d <;> exact no h rfl

/-- Every edge on the actual selected atom lookup is retained. Cycles or
additional unused sibling branches in the surrounding host are permitted. -/
theorem atom_trace_not_hole {a b : (C.expand R).Edge} {n}
    (retained : ∀ h, C.edgeLabel a.1 ≠ primitiveLabel d (.hole h))
    (path : Trace (StoreTrace.Hop (C.expand R)) a b n) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  induction path with
  | refl => exact retained
  | step hop path ih => exact ih (atom_hop_not_hole C cert rightClosed retained hop)

/-- Full primitive labels in an original local occurrence preserve its exact
atom-hop path, so the selection can be checked in the smaller rule graph. -/
theorem matched_atom_trace_not_hole {J K} {A : Hypernet d J K}
    (f : MatchEmbedding A (C.expand R)) {a b n}
    (retained : ∀ h, C.edgeLabel (f.edges a).1 ≠ primitiveLabel d (.hole h))
    (path : Trace (StoreTrace.Hop A) a b n) :
    ∀ h, C.edgeLabel (f.edges b).1 ≠ primitiveLabel d (.hole h) := by
  apply atom_trace_not_hole C cert rightClosed retained
  apply path.map f.edges
  intro a b hop
  refine ⟨?_,f.adjacent hop.2⟩
  rcases hop.1 with label | label | label
  · exact .inl (f.primitive a _ label)
  · exact .inr (.inl (f.primitive a _ label))
  · exact .inr (.inr (f.primitive a _ label))

end Hypernets.Copying.CopyingTemplate.ConverseOverlap
