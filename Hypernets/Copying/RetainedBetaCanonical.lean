import Hypernets.Copying.RetainedBetaOpening

/-! Complete cuts realize the argument-exposing beta frame in any host.
Actual original beta successors are identified with this canonical whole-
graph opening through independently checked opening certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph Application
variable {d I O J K k h} {A X : Hypernet (d+1) J K} {G : Hypernet (d+1) I O}
    (f : Occurrence A G) {v : A.Vertex} {w : X.Vertex}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- A geometric opening certificate transports through the actual finite
complement of a complete occurrence, retaining every unmatched host edge. -/
noncomputable def openingCertificate (a : OpeningCertificate A X v w B) :
    OpeningCertificate G (CompleteMatchCut.replaceWith f.matchEmbedding f.label X)
      (f.ports v) (CompleteMatchCut.replacePort f.matchEmbedding f.label X w) B := by
  have cast := a.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
    (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm
  have plugged := cast.plug (CompleteMatchCut.net f.matchEmbedding f.label) none
  have actual := plugged.rename (CompleteMatchCut.realization f.matchEmbedding f.label)
    (DeepIso.refl (CompleteMatchCut.replaceWith f.matchEmbedding f.label X))
  have token := CompleteMatchCut.map_insert f.matchEmbedding f.label v
  change Port.map (CompleteMatchCut.realization f.matchEmbedding f.label).vertices.toFun _ = f.ports v at token
  rw [← token]
  simpa only [CompleteMatchCut.replacement,CompleteMatchCut.replacePort,
    DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using actual
end Hypernets.Copying.Opening.Occurrence

namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening Combined
variable {d I O k h} {G : Hypernet (d+1) I O} {v : G.Vertex}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)} (a : Match G v B)

/-- Only the app/lambda/box footprint is replaced. The original argument,
its arbitrary surrounding family and all other host edges remain intact. -/
noncomputable def canonical : Combined.State (d+1) I O :=
  ⟨CompleteMatchCut.replaceWith (occurrence B a).matchEmbedding (occurrence B a).label (openBody B),
    (.search,CompleteMatchCut.replacePort (occurrence B a).matchEmbedding (occurrence B a).label
      (openBody B) (.input 0))⟩

/-- The canonical graph has the complete original source-relative opening
certificate, including its exact resumed token. -/
noncomputable def canonical_certificate :
    OpeningCertificate G (canonical a).1 v (canonical a).2.2 B :=
  (occurrence B a).openingCertificate (certificate B)

/-- Every actual original beta successor is the canonical cut opening up to
recursive graph representation. The actual rule's stability is preserved in
its supplied rewrite; no stability of the exposed frame is asserted. -/
theorem rewrite_canonical {H : Hypernet (d+1) I O} {w : H.Vertex}
    (step : Rewrite G v H w) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ (canonical a)) :=
  (rewrite_application_certificate step ⟨a.app,a.head_at,trivial⟩).coherent
    (.certificate (canonical_certificate a))
end Hypernets.Copying.Application.RetainedFrame
