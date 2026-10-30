import Hypernets.Copying.CommonContextTransfer
import Hypernets.Copying.CopyingResidualBoundary

/-! The original finite common-context cut lifts a remote copying diagram
with exact sharing corrections on either endpoint. Selected shallow holes
are allowed inside the matched common context; every unmatched original
recursive contribution remains in the copying specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteCut
open Graph Opening Combined CommonContextCut
variable {d I O} (C : Hypernet d I O) {J K} {A : Hypernet d J K}
    (f : Occurrence A C)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    {X Y : Hypernet d J K} {v : X.Vertex} {w : Y.Vertex}

/-- The actual two-sided local residual is inserted in the complete cut,
retaining literal original certificates at every other context edge. -/
noncomputable def residual (p : TwoSidedResidual X v Y w) :
    TwoSidedResidual (afterGraph C f L X) (afterPort C f L X v)
      (afterGraph C f R Y) (afterPort C f R Y w) := by
  exact TwoSidedResidual.expandSelected (frame C f) (afterFamily C f L X)
    (afterFamily C f R Y) none
    (p.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)
    (by
      intro e ne
      cases e with
      | none => exact (ne rfl).elim
      | some e => exact FillingWitness.originalEdge (cert e.val) free)

include cert free in
/-- Both original whole-graph rewrites and their corrected original specimen
are constructed from the same finite common-context occurrence. -/
theorem diagram {a : A.Vertex}
    (left : Rewrite ((skeleton C f).expand (localFamily C f L))
      (Net.Expansion.host (skeleton C f) (localFamily C f L) a) X v)
    (right : Rewrite ((skeleton C f).expand (localFamily C f R))
      (Net.Expansion.host (skeleton C f) (localFamily C f R) a) Y w)
    (p : TwoSidedResidual X v Y w) :
    Rewrite (C.expand L) (Net.Expansion.host C L (f.ports a))
      (afterGraph C f L X) (afterPort C f L X v) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R (f.ports a))
      (afterGraph C f R Y) (afterPort C f R Y w) ∧
    Nonempty (TwoSidedResidual (afterGraph C f L X) (afterPort C f L X v)
      (afterGraph C f R Y) (afterPort C f R Y w)) :=
  ⟨rewrite_at C f L left,rewrite_at C f R right,⟨residual C f cert free p⟩⟩

end Hypernets.Copying.CopyingTemplate.RemoteCut
