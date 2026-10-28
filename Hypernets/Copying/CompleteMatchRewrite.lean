import Hypernets.Copying.CompleteMatchRealization
import Hypernets.Copying.CombinedPadding
import Hypernets.Copying.OpeningOccurrence

/-! Complete incidence matches support actual whole-graph rewrites. The finite
complement is constructed, and the source token is the original matched port;
no context decomposition or locality certificate is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace CompleteMatchCut
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))

/-- Replace exactly the matched source, retaining its computed complement. -/
noncomputable def replaceWith (B : Hypernet d J K) : Hypernet d I O :=
  (net f labels).plug none (B.reboundary (hole_input f labels).symm (hole_output f labels).symm)

/-- Attach the successor's resumed token at the unchanged hole boundary. -/
noncomputable def replacePort (B : Hypernet d J K) (w : B.Vertex) :
    (replaceWith f labels B).Vertex :=
  Net.Replacement.insert (net f labels) none
    (B.reboundary (hole_input f labels).symm (hole_output f labels).symm)
    (Port.cast (hole_input f labels).symm (hole_output f labels).symm w)

/-- Any proved rewrite on a complete matched source is a genuine rewrite of
the original host. The complement and every boundary attachment are explicit. -/
theorem rewrite {B : Hypernet d J K} {v : A.Vertex} {w : B.Vertex}
    (step : Combined.Rewrite A v B w) :
    Combined.Rewrite G (f.ports v) (replaceWith f labels B) (replacePort f labels B w) := by
  have castStep := Combined.rewrite_reboundary
    (hole_input f labels).symm (hole_output f labels).symm step
  have plugged := Combined.Rewrite.plug (net f labels) none castStep
  have actual := plugged.rename (realization f labels) (DeepIso.refl (replaceWith f labels B))
  have token := map_insert f labels v
  change Port.map (realization f labels).vertices.toFun _ = f.ports v at token
  rw [← token]
  simpa only [replacement,replacePort,DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq]
    using actual

/-- In particular every member of the unchanged local-rule relation can fire
at any complete occurrence, with its original stability premises intact. -/
theorem local_rewrite {B : Hypernet d J K} {v : A.Vertex} {w : B.Vertex}
    (step : Combined.Local A v B w) :
    Combined.Rewrite G (f.ports v) (replaceWith f labels B) (replacePort f labels B w) :=
  rewrite f labels (.local step)

end CompleteMatchCut

namespace Opening.Occurrence
variable {d I O J K} {A B : Hypernet d J K} {G : Hypernet d I O}
    (f : Occurrence A G)

/-- Existing complete occurrences use the constructed complement directly. -/
theorem rewrite {v : A.Vertex} {w : B.Vertex} (step : Combined.Rewrite A v B w) :
    Combined.Rewrite G (f.ports v)
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label B)
      (CompleteMatchCut.replacePort f.matchEmbedding f.label B w) :=
  CompleteMatchCut.rewrite f.matchEmbedding f.label step

theorem local_rewrite {v : A.Vertex} {w : B.Vertex} (step : Combined.Local A v B w) :
    Combined.Rewrite G (f.ports v)
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label B)
      (CompleteMatchCut.replacePort f.matchEmbedding f.label B w) :=
  f.rewrite (.local step)

end Opening.Occurrence
end Hypernets.Copying
