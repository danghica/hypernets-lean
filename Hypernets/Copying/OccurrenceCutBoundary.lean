import Hypernets.Copying.BoxPullContractionCutLinks

/-! Complete disjoint occurrences retain their original external input and
output attachments under an actual computed cut replacement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O J K L M} {A : Hypernet d J K} {B : Hypernet d L M}
    {G : Hypernet d I O} (f : Occurrence A G) (g : Occurrence B G)
    (apart : ∀ e a, f.edges e ≠ g.edges a) (N : Hypernet d J K)

theorem acrossCut_input {v : B.Vertex} {i : Fin I.length} (attached : g.ports v = .input i) :
    (f.acrossCut g apart N).ports v = .input i := by
  have point : cutPort f g apart v = .input i := by
    apply CompleteMatchCut.embed_injective f.matchEmbedding
    exact (CompleteMatchCut.embed_project _ _ _).trans attached
  change Net.Replacement.host (CompleteMatchCut.net f.matchEmbedding f.label) none _ (cutPort f g apart v) = _
  rw [point]
  rfl

theorem acrossCut_output {v : B.Vertex} {i : Fin O.length} (attached : g.ports v = .output i) :
    (f.acrossCut g apart N).ports v = .output i := by
  have point : cutPort f g apart v = .output i := by
    apply CompleteMatchCut.embed_injective f.matchEmbedding
    exact (CompleteMatchCut.embed_project _ _ _).trans attached
  change Net.Replacement.host (CompleteMatchCut.net f.matchEmbedding f.label) none _ (cutPort f g apart v) = _
  rw [point]
  rfl

end Hypernets.Copying.Opening.Occurrence
