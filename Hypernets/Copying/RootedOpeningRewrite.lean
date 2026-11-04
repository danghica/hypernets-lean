import Hypernets.Copying.RetainedBetaEnabled

/-! A complete original opening certificate and actual rooted search produce
an original beta rewrite to its certified target, without assuming stability
of any exposed local argument boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.OpeningCertificate
open Graph Combined
variable {d I O k h} {G H : Hypernet (d+1) I O} {v : G.Vertex} {w : H.Vertex}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- Original rooted readiness supplies the full stable argument, after which
source-determined opening coherence fixes the exact certified successor. -/
theorem rooted_rewrite (a : OpeningCertificate G H v w B) {i : Fin I.length}
    (rooted : Search.RootedFrom G i (.rewrite,v)) : Rewrite G v H w := by
  obtain ⟨K,u,step⟩ := RetainedFrame.rooted_enabled B G a.matched rooted
  obtain ⟨iso⟩ := (rewrite_application_certificate step
    ⟨a.matched.app,a.matched.head_at,trivial⟩).coherent (.certificate a)
  have actual := step.rename (DeepIso.refl G) iso.graph
  have token : Port.map iso.graph.vertices.toFun u = w := iso.vertex
  simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq,token] using actual
end Hypernets.Copying.Application.OpeningCertificate
