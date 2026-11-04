import Hypernets.Copying.RetainedBetaCanonical
import Hypernets.Copying.RetainedFrameTransfer

/-! Lift complete beta-opening certificates through the actual retained
footprint complement. The argument may remain in an unrelated shallow
filling: certificates describe geometry, while actual original rewrites
supply stability and are compared by proved source-determined coherence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined Application
variable {d I O} (C : Hypernet (d+1) I O)
    {L R : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet (d+1) J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding)
    {k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- The complete source-relative opening certificate lifts through the real
common complement with every unmatched recursive contribution unchanged. -/
noncomputable def frame_opening
    (F : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) {X : Hypernet (d+1) J K} {a b}
    (opening : OpeningCertificate ((skeleton C f cert avoid).expand (localFamily C f cert avoid F)) X a b B) :
    OpeningCertificate (C.expand F) (afterGraph C f cert avoid F X)
      (Port.map (frameIso C f cert avoid F).vertices.toFun
        (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) none
          (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm a)))
      (afterPort C f cert avoid F X b) B := by
  have cast := opening.reboundary
    (CompleteMatchCut.hole_input (skeletonOccurrence C f cert avoid).matchEmbedding
      (skeletonOccurrence C f cert avoid).label).symm
    (CompleteMatchCut.hole_output (skeletonOccurrence C f cert avoid).matchEmbedding
      (skeletonOccurrence C f cert avoid).label).symm
  have lifted := OpeningCertificate.expand (frame C f cert avoid) (grouped C f cert avoid F)
    (afterFamily C f cert avoid F X) none
    (by intro e ne; cases e with | none => exact False.elim (ne rfl) | some e => rfl) cast
  have actual := lifted.rename (frameIso C f cert avoid F) (DeepIso.refl (afterGraph C f cert avoid F X))
  simpa only [afterPort,DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using actual

/-- The left certificate starts at the exact original matched token. -/
noncomputable def left_opening {X : Hypernet (d+1) J K} {a : A.Vertex} {b : X.Vertex}
    (opening : OpeningCertificate A X a b B) :
    OpeningCertificate (C.expand L) (afterGraph C f cert avoid L X)
      (f.ports a) (afterPort C f cert avoid L X b) B := by
  have normalized := opening.rename (reconstruction C f cert avoid).symm (DeepIso.refl X)
  have lifted := frame_opening C f cert avoid L normalized
  have eq : Port.map (frameIso C f cert avoid L).vertices.toFun
      (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid L) none
        (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
          (Port.map (reconstruction C f cert avoid).vertices.invFun a))) = f.ports a := by
    rw [reconstruction_inverse]
    exact (frame_local_host C f cert avoid L a).trans (host_port C f.matchEmbedding cert avoid a)
  simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,DeepIso.symm,Net.RelIso.symm,Bijection.symm,
    Port.map_id_fun,id_eq,eq] using lifted

/-- The paired right certificate starts at the same original specimen wire,
including when the stable operand belongs to a shallow external family. -/
noncomputable def right_opening_at {Y : Hypernet (d+1) J K} {a : A.Vertex} {u : Y.Vertex} {q : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L q)
    (opening : OpeningCertificate ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) Y
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a) u B) :
    OpeningCertificate (C.expand R) (afterGraph C f cert avoid R Y)
      (Net.Expansion.host C R q) (afterPort C f cert avoid R Y u) B := by
  have lifted := frame_opening C f cert avoid R opening
  have portEq : (skeletonOccurrence C f cert avoid).ports a = q :=
    Net.Expansion.host_injective C L ((host_port C f.matchEmbedding cert avoid a).trans attached)
  have eq := (frame_local_host C f cert avoid R a).trans (congrArg (Net.Expansion.host C R) portEq)
  exact Eq.mp (congrArg (fun v => OpeningCertificate (C.expand R)
    (afterGraph C f cert avoid R Y) v (afterPort C f cert avoid R Y u) B) eq) lifted

/-- Every supplied actual original beta successor agrees with the explicitly
framed opening and resumed token. No new operational opening rule is used. -/
theorem left_opening_successor {X : Hypernet (d+1) J K} {a : A.Vertex} {b : X.Vertex}
    {H : Hypernet (d+1) I O} {w : H.Vertex}
    (opening : OpeningCertificate A X a b B)
    (actual : Rewrite (C.expand L) (f.ports a) H w) :
    Nonempty (StateIso ⟨H,(.search,w)⟩
      ⟨afterGraph C f cert avoid L X,(.search,afterPort C f cert avoid L X b)⟩) := by
  let lifted := left_opening C f cert avoid opening
  exact (rewrite_application_certificate actual
    ⟨lifted.matched.app,lifted.matched.head_at,trivial⟩).coherent (.certificate lifted)

/-- The same representation-independent comparison holds for an independently
supplied original right successor at the actual paired specimen token. -/
theorem right_opening_successor {Y : Hypernet (d+1) J K} {a : A.Vertex} {u : Y.Vertex} {q : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L q)
    (opening : OpeningCertificate ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) Y
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a) u B)
    {H : Hypernet (d+1) I O} {w : H.Vertex}
    (actual : Rewrite (C.expand R) (Net.Expansion.host C R q) H w) :
    Nonempty (StateIso ⟨H,(.search,w)⟩
      ⟨afterGraph C f cert avoid R Y,(.search,afterPort C f cert avoid R Y u)⟩) := by
  let lifted := right_opening_at C f cert avoid attached opening
  exact (rewrite_application_certificate actual
    ⟨lifted.matched.app,lifted.matched.head_at,trivial⟩).coherent (.certificate lifted)

end Hypernets.Copying.RetainedFootprint
