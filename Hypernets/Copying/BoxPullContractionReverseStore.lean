import Hypernets.Copying.BoxPullContractionReverseStoreFootprint
import Hypernets.Copying.RetainedRewriteTransfer

/-! Actual left-side store rewrites are reconstructed from every original
right-side BPullC store match. No off-spine sharing overlap is assumed absent. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseStore
open Graph Opening Combined
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {v : C.Vertex}
include cert closed

theorem read_enabled {h} (tree : ContractionTree .atom (h+1))
    (f : Occurrence (Dereference.before tree d) (C.expand R))
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  obtain ⟨m,U,g,point,avoid⟩ := ReverseStoreFootprint.read_occurrence C cert closed tree f attached
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) g.matchEmbedding avoid
    (BoxPermutation.PrimitiveFootprint.dereference U d) (.read U d) point

theorem assignment_enabled {h J} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] J) (stable : Stable G)
    (f : Occurrence (Assignment.before tree G) (C.expand R))
    (attached : f.ports (Assignment.inputPort h J 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  obtain ⟨m,U,g,point,avoid⟩ := ReverseStoreFootprint.assignment_occurrence C cert closed tree G stable f attached
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) g.matchEmbedding avoid
    (BoxPermutation.PrimitiveFootprint.assignment U G stable) (.assign U G stable) point

theorem same_enabled {h} (tree : ContractionTree .atom (h+2))
    (f : Occurrence (AtomEquality.Same.before tree d) (C.expand R))
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  obtain ⟨m,U,g,point,avoid⟩ := ReverseStoreFootprint.same_occurrence C cert closed tree f attached
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) g.matchEmbedding avoid
    (BoxPermutation.PrimitiveFootprint.same U d) (.same U d) point

theorem different_enabled {h k} (tree : ContractionTree .atom (h+1)) (other : ContractionTree .atom (k+1))
    (f : Occurrence (AtomEquality.Different.before tree other d) (C.expand R))
    (attached : f.ports (AtomEquality.Different.inputPort h k 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  obtain ⟨m,n,U,V,g,point,avoid⟩ := ReverseStoreFootprint.different_occurrence C cert closed tree other f attached
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) g.matchEmbedding avoid
    (BoxPermutation.PrimitiveFootprint.different U V d) (.different U V d) point

end Hypernets.Copying.BoxPullContraction.ReverseStore
