import Hypernets.Copying.RetainedFootprint
import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.PrimitiveRuleFootprints

/-! Primitive-footprint transfer produces original whole-graph rewrites, not
only matches. The footprint exclusion is explicit; paired residual specimens
remain a separate obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- For a primitive source, incidence matching already includes every full
recursive label: there are no box bodies to reconstruct. -/
theorem MatchEmbedding.primitive_labels {d I O J K} {A : Hypernet d J K}
    {G : Hypernet d I O} (f : MatchEmbedding A G)
    (primitive : BoxPermutation.PrimitiveFootprint A) :
    ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)) := by
  intro e
  obtain ⟨p,label⟩ := primitive e
  rw [f.primitive e p label,label]
  exact labelEquiv_refl d _

namespace RetainedFootprint
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    {J K} {A B : Hypernet d J K} (f : MatchEmbedding A (C.expand L))
    (avoid : AvoidsShallow C f)
include cert avoid

/-- Transfer a proved primitive-source rewrite across arbitrary paired
fillings. The other-side complement is constructed from the actual match. -/
theorem primitive_rewrite (primitive : BoxPermutation.PrimitiveFootprint A)
    {a : A.Vertex} {b : B.Vertex} (step : Combined.Rewrite A a B b)
    {v : C.Vertex} (attached : f.ports a = Net.Expansion.host C L v) :
    ∃ H : Hypernet d I O, ∃ w,
      Combined.Rewrite (C.expand R) (Net.Expansion.host C R v) H w := by
  let other := across C f cert avoid
  have actual := CompleteMatchCut.rewrite other (other.primitive_labels primitive) step
  rw [across_host C f cert avoid attached] at actual
  exact ⟨_,_,actual⟩

/-- In particular this applies to the original allocation, store, equality and
arithmetic local rules after their no-shallow-overlap obligation is discharged. -/
theorem primitive_local (primitive : BoxPermutation.PrimitiveFootprint A)
    {a : A.Vertex} {b : B.Vertex} (step : Combined.Local A a B b)
    {v : C.Vertex} (attached : f.ports a = Net.Expansion.host C L v) :
    ∃ H : Hypernet d I O, ∃ w,
      Combined.Rewrite (C.expand R) (Net.Expansion.host C R v) H w :=
  primitive_rewrite C cert f avoid primitive (.local step) attached

end RetainedFootprint
end Hypernets.Copying
