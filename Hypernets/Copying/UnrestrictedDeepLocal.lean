import Hypernets.Copying.UnrestrictedLocalTransfer

/-! Genuine paired beta and copying reducts for arbitrary-template fillings.
All body certificates come from the actual complete occurrence and finite cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.UnrestrictedResidual
open Graph Combined RetainedFootprint

/-- The original arbitrary beta body may contain arbitrary recursive fillings.
Padding closure is the only template law needed to open that body. -/
theorem beta_local {T : PreTemplate} {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (padding : T.PaddingClosed)
    (free : FocusFree C) {k h K}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input 0)) H (.input 0) ∧
      Nonempty (FillingWitness T (Application.after B G) H) := by
  obtain ⟨H,step,⟨w⟩⟩ := UnrestrictedLocalTransfer.Beta.transport B G (UnrestrictedFootprint.decoration C f cert avoid free)
    padding stable (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free).1)
  have actual := step.rename (UnrestrictedFootprint.decorationIso C f cert avoid free) (DeepIso.refl H)
  rw [UnrestrictedFootprint.decorationIso_host] at actual
  exact ⟨H,actual,⟨w⟩⟩

/-- Every original copyable constructor transfers through the retained source,
including active primitive operations and arbitrary recursively filled lambdas. -/
theorem copying_local {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    (free : FocusFree C) {n k h}
    (tree : ContractionTree .term (n+1)) (G : Hypernet d [.term] (environmentInterface k h))
    (copyable : Copyable G) (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input ⟨0,by simp⟩))
      H (.input ⟨0,by simp⟩) ∧ Nonempty (FillingWitness T (CopyRule.after tree G) H) := by
  obtain ⟨H,step,⟨w⟩⟩ := UnrestrictedLocalTransfer.Copying.transport copyable tree
    (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free).1)
    (UnrestrictedFootprint.decoration C f cert avoid free)
  have actual := step.rename (UnrestrictedFootprint.decorationIso C f cert avoid free) (DeepIso.refl H)
  rw [UnrestrictedFootprint.decorationIso_host] at actual
  exact ⟨H,actual,⟨w⟩⟩
end Hypernets.Copying.UnrestrictedResidual
