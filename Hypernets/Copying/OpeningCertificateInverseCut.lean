import Hypernets.Copying.RetainedBetaCanonical

/-! A complete occurrence of an opened body determines the actual inverse
frame complement. This constructs an opening certificate, not a new rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph Application
variable {d I O J K m n}
    {A : Hypernet (d+1) J K} {G : Hypernet (d+1) I O} (f : Occurrence A G)
    {B : Hypernet d [.term] (environmentInterface (m+1) n)}

/-- Insert the original source of a geometric opening into the computed
complement of its actual target. Every unmatched edge and port is retained. -/
noncomputable def opening_into {X : Hypernet (d+1) J K} {v : X.Vertex} {w : A.Vertex}
    (opening : OpeningCertificate X A v w B) :
    OpeningCertificate
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label X) G
      (CompleteMatchCut.replacePort f.matchEmbedding f.label X v) (f.ports w) B := by
  have cast := opening.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
    (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm
  have plugged := cast.plug (CompleteMatchCut.net f.matchEmbedding f.label) none
  have actual := plugged.rename (DeepIso.refl _) (CompleteMatchCut.realization f.matchEmbedding f.label)
  have token := CompleteMatchCut.map_insert f.matchEmbedding f.label w
  change Port.map (CompleteMatchCut.realization f.matchEmbedding f.label).vertices.toFun _ = f.ports w at token
  rw [← token]
  simpa only [CompleteMatchCut.replacement,CompleteMatchCut.replaceWith,CompleteMatchCut.replacePort,
    DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using actual

end Hypernets.Copying.Opening.Occurrence
