import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.BoundaryIso

/-! Boundary actions also give complete local occurrences. The occurrence
records their actual boundary action instead of silently fixing those ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph

/-- Full recursive labels upgrade the existing typed boundary transport to
an actual complete occurrence, with no extra injectivity assumptions. -/
noncomputable def ofBoundaryIso {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) : Occurrence G H :=
  (MatchEmbedding.ofTransport (Search.ofBoundaryIso f)).occurrence f.edge_label
end Hypernets.Copying.Opening.Occurrence
