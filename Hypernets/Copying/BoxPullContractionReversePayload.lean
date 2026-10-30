import Hypernets.Copying.BoxPullContractionReverseCopySpine

/-! Reflection of literal primitive copyable payloads at their original common
incoming wire. The entire ordered output interface is preserved. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseCopy
open Graph Opening
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {v : C.Vertex}
include cert closed

/-- A primitive payload has a single sourced edge and therefore cannot be
introduced by the shallow right-hand contraction/box replacement. -/
theorem plain_avoids (code : CopyRule.PlainCode)
    (f : Occurrence (code.net d) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  apply ReversePrimitive.sourced_ancestors_avoid C cert closed f
    (by cases code <;> exact BoxPermutation.PrimitiveFootprint.primitive d _)
    (code.head d).2 _ attached
  intro e
  have same : e = code.edge d := by
    cases d <;> cases code <;> exact Fin.ext (by have := e.isLt; omega)
  subst e
  exact .refl _

/-- The original primitive source is reconstructed as a full left occurrence,
not merely as an operation label or an abstract matching assumption. -/
theorem reflect_plain (code : CopyRule.PlainCode)
    (f : Occurrence (code.net d) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ g : Occurrence (code.net d) (C.expand L),
      g.ports (.input 0) = Net.Expansion.host C L v := by
  let m := RetainedFootprint.across C f.matchEmbedding (fun e => (cert e).converse)
    (plain_avoids C cert closed code f attached)
  let g := m.occurrence (m.primitive_labels (by
    cases code <;> exact BoxPermutation.PrimitiveFootprint.primitive d _))
  exact ⟨g,RetainedFootprint.across_host C f.matchEmbedding (fun e => (cert e).converse)
    (plain_avoids C cert closed code f attached) attached⟩

end Hypernets.Copying.BoxPullContraction.ReverseCopy
