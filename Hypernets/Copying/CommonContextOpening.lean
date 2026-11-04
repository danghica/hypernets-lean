import Hypernets.Copying.CommonContextTransfer
import Hypernets.Copying.RetainedBetaCanonical

/-! Original geometric beta certificates lift through a common-context cut
that may contain entire shallow template components. Actual rooted search,
not a local stability assumption, supplies the host beta transition. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Combined Application
variable {d I O} (C : Hypernet (d+1) I O) {J K} {A : Hypernet (d+1) J K}
    (f : Opening.Occurrence A C)
    (F : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e)))
    {k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)}

noncomputable def frame_opening {X : Hypernet (d+1) J K} {a b}
    (opening : OpeningCertificate ((skeleton C f).expand (localFamily C f F)) X a b B) :
    OpeningCertificate (C.expand F) (afterGraph C f F X)
      (Port.map (frameIso C f F).vertices.toFun
        (Net.Expansion.insert (frame C f) (grouped C f F) none
          (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm a)))
      (afterPort C f F X b) B := by
  have cast := opening.reboundary
    (CompleteMatchCut.hole_input (skeletonOccurrence C f).matchEmbedding (skeletonOccurrence C f).label).symm
    (CompleteMatchCut.hole_output (skeletonOccurrence C f).matchEmbedding (skeletonOccurrence C f).label).symm
  have lifted := OpeningCertificate.expand (frame C f) (grouped C f F) (afterFamily C f F X) none
    (by intro e ne; cases e with | none => exact False.elim (ne rfl) | some e => rfl) cast
  have actual := lifted.rename (frameIso C f F) (DeepIso.refl (afterGraph C f F X))
  simpa only [afterPort,DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using actual

/-- The active token is the exact old common-context coordinate, even when
another shallow family supplies the argument outside the selected fragment. -/
noncomputable def opening_at {X : Hypernet (d+1) J K} {a : A.Vertex} {b : X.Vertex}
    (opening : OpeningCertificate ((skeleton C f).expand (localFamily C f F)) X
      (Net.Expansion.host (skeleton C f) (localFamily C f F) a) b B) :
    OpeningCertificate (C.expand F) (afterGraph C f F X)
      (Net.Expansion.host C F (f.ports a)) (afterPort C f F X b) B := by
  have lifted := frame_opening C f F opening
  exact Eq.mp (congrArg (fun v => OpeningCertificate (C.expand F)
    (afterGraph C f F X) v (afterPort C f F X b) B) (frame_local_host C f F a)) lifted

/-- Any actual original beta successor has the computed whole-graph opening
and resume token, by the original source-determined opening coherence. -/
theorem opening_successor {X : Hypernet (d+1) J K} {a : A.Vertex} {b : X.Vertex}
    (opening : OpeningCertificate ((skeleton C f).expand (localFamily C f F)) X
      (Net.Expansion.host (skeleton C f) (localFamily C f F) a) b B)
    {H : Hypernet (d+1) I O} {w : H.Vertex}
    (actual : Rewrite (C.expand F) (Net.Expansion.host C F (f.ports a)) H w) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨afterGraph C f F X,(.search,afterPort C f F X b)⟩) := by
  let lifted := opening_at C f F opening
  exact (rewrite_application_certificate actual
    ⟨lifted.matched.app,lifted.matched.head_at,trivial⟩).coherent (.certificate lifted)
end Hypernets.Copying.CommonContextCut
