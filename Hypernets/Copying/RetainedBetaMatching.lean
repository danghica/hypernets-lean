import Hypernets.Copying.RetainedBetaFrameTransfer
import Hypernets.Copying.RetainedBetaDecoration
import Hypernets.Copying.RetainedBetaEnabled
import Hypernets.Copying.AllContextResiduals
import Hypernets.Copying.FramedFillingTransfer

/-! Complete exact matching for the retained/deep app-lambda-box footprint.
The whole actual argument, including any shallow multi-input lambda family,
is retained in the computed complement and is never assumed to be a local
paired filling. Actual rooted search independently enables the original rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening Combined RetainedFootprint
variable {T : PreTemplate} {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    (padding : T.PaddingClosed) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (f : Occurrence (net B) (C.expand L)) (avoid : AvoidsShallow C f.matchEmbedding)
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))
include cert free padding closed leftClosed rightClosed avoid attached leftRoot rightRoot

/-- Every retained app/lambda/box match gives two actual one-step original
beta successors and an exact original recursive quasi-specimen. The boxed
body may contain arbitrary deep template fillings. -/
theorem matching :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  let D := UnrestrictedFootprint.decoration C f cert avoid free
  have frameFree : FocusFree (net B) :=
    f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free).1
  obtain ⟨E,⟨localRight⟩,⟨w⟩⟩ := paired_opening B D padding frameFree
  have changed := localRight.rename (UnrestrictedFootprint.decorationIso C f cert avoid free)
    (DeepIso.refl (openBody E))
  rw [UnrestrictedFootprint.decorationIso_host] at changed
  have leftCert : OpeningCertificate (C.expand L) (afterGraph C f cert avoid L (openBody B))
      (Net.Expansion.host C L v) (afterPort C f cert avoid L (openBody B) (.input 0)) B :=
    attached ▸ left_opening C f cert avoid (certificate B)
  have rightCert := right_opening_at C f cert avoid attached changed
  obtain ⟨H,a,left⟩ := rooted_enabled B (C.expand L) leftCert.matched leftRoot
  obtain ⟨K,b,right⟩ := rooted_enabled E (C.expand R) rightCert.matched rightRoot
  obtain ⟨li⟩ := (rewrite_application_certificate left
    ⟨leftCert.matched.app,leftCert.matched.head_at,trivial⟩).coherent (.certificate leftCert)
  obtain ⟨ri⟩ := (rewrite_application_certificate right
    ⟨rightCert.matched.app,rightCert.matched.head_at,trivial⟩).coherent (.certificate rightCert)
  have lc : HoleFree (afterGraph C f cert avoid L (openBody B)) :=
    (allLabels_iso_iff _ li.graph).mp (rewrite_holeFree left leftClosed)
  have rc : HoleFree (afterGraph C f cert avoid R (openBody E)) :=
    (allLabels_iso_iff _ ri.graph).mp (rewrite_holeFree right rightClosed)
  have pair := pointedResidual_allContexts_quasi C f cert avoid free w closed lc rc
    .search (.input 0) rfl (by intro eq; cases eq)
  have leq : StateClass.ofState ⟨d+1,H,(.search,a)⟩ = StateClass.ofState
      ⟨d+1,afterGraph C f cert avoid L (openBody B),(.search,afterPort C f cert avoid L (openBody B) (.input 0))⟩ :=
    Quotient.sound (.iso (.lift li))
  have req : StateClass.ofState ⟨d+1,K,(.search,b)⟩ = StateClass.ofState
      ⟨d+1,afterGraph C f cert avoid R (openBody E),(.search,afterPort C f cert avoid R (openBody E) (.input 0))⟩ :=
    Quotient.sound (.iso (.lift ri))
  refine ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),?_⟩
  rw [leq,req]
  simpa only [FillingWitness.leftPosition_input,FillingWitness.rightPosition_input] using pair

/-- Exact retained-beta robustness applies to any independently represented
successor of the original combined machine, with no argument-retention law. -/
theorem robust_case (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,pair⟩ := matching C cert free padding closed leftClosed rightClosed B f avoid attached leftRoot rightRoot
  exact FillingWitness.matching_robust_case Q P U left right pair step

/-- The same exact paired construction covers every independently supplied
opposite successor, without exchanging or approximating beta stability. -/
theorem converse_robust_case (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,pair⟩ := matching C cert free padding closed leftClosed rightClosed B f avoid attached leftRoot rightRoot
  exact FillingWitness.matching_robust_case Q P U right left
    (FillingWitness.quasi_exchange _ pair) step

end Hypernets.Copying.Application.RetainedFrame
