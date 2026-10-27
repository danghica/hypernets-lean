import Hypernets.Copying.StoreRefocusing

/-! The complete application-opening certificate replays the pre-application search. -/
namespace Hypernets.Copying.Application.OpeningCertificate
open Graph Search Opening

/-- Before the application request, search has not used its app/lambda/box frame. -/
theorem rooted {d I O k h} {G H : Hypernet (d+1) I O} {v w i}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : OpeningCertificate G H v w B) (root : RootedFrom G i (.rewrite,v)) :
    RootedFrom H i (.search,w) := by
  apply rooted_of_frames (Port.map (fun x : G.Internal => (Sum.inl x : G.Internal ⊕ (openBody B).Internal)))
    (Port.map a.realization.vertices) (fun _ _ h => Port.map_injective a.realization.vertex_injective h) rfl a.token ?_ root
  intro n p hist avoid e primitive label active used
  have source := operation_source a.matched.head_at.1 a.matched.head_at.2
  have na : e ≠ a.matched.app := by
    intro eq; subst e
    exact avoid (uses_visit hist source used)
  have nl : e ≠ a.matched.lam := by
    intro eq; subst e
    exact avoid (uses_parent_visit hist a.matched.lambda_source used source (by rw [a.matched.app_target]; simp))
  have nb : e ≠ a.matched.boxEdge := by
    intro eq; subst e
    have bad := (primitive_equiv a.matched.box_label primitive).mp label
    cases bad
  obtain ⟨b,eb⟩ := (a.realization.edge_range (.inl e)).mpr ⟨na,nl,nb⟩
  refine ⟨b,?_,?_,?_⟩
  · have rel := a.realization.edge_label b
    rw [eb] at rel
    exact (primitive_equiv rel primitive).mpr label
  · rw [a.realization.source,eb]
  · rw [a.realization.target,eb]
end Hypernets.Copying.Application.OpeningCertificate

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- Actual micro-beta in every host is refocusing, with its stable-argument premise retained. -/
theorem application_rooted {d I O} {G H : Hypernet d I O} {v w e i}
    (head : HeadAt G v e (.operation .app)) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  have witness := rewrite_application_certificate step ⟨e,head,trivial⟩
  cases witness with | certificate a => exact a.rooted root
end Hypernets.Copying.Combined
