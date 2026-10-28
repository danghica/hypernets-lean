import Hypernets.Copying.NullaryDeepOverlap
import Hypernets.Copying.GenericRetainedLocal

/-! Genuine paired beta and copying reducts for nullary-template fillings.
All body certificates come from the actual complete occurrence and finite cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.NullaryResidual
open Graph Combined RetainedFootprint

/-- The original arbitrary beta body may contain recursive nullary fillings.
Padding closure is the only template law needed to open that body. -/
theorem beta_local {T : PreTemplate} {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs) (padding : T.PaddingClosed)
    (free : FocusFree C) (closed : HoleFree (C.expand L)) {k h K}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input 0)) H (.input 0) ∧
      Nonempty (FillingWitness T (Application.after B G) H) := by
  have binding := (DeepFilling.expand C L R cert).nullary_bindingFree none free closed
  obtain ⟨H,step,⟨w,_⟩⟩ := RetainedLocalTransfer.Beta.transport B G (decoration C f cert avoid binding)
    padding stable (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free).1) (f.allLabels _ closed)
  have actual := step.rename (decorationIso C f cert avoid binding) (DeepIso.refl H)
  rw [decorationIso_host] at actual
  exact ⟨H,actual,⟨w⟩⟩

/-- Every original copyable constructor transfers through the retained source,
including active primitive operations and arbitrary recursively filled lambdas. -/
theorem copying_local {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
    (free : FocusFree C) (closed : HoleFree (C.expand L)) {n k h}
    (tree : ContractionTree .term (n+1)) (G : Hypernet d [.term] (environmentInterface k h))
    (copyable : Copyable G) (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input ⟨0,by simp⟩))
      H (.input ⟨0,by simp⟩) ∧ Nonempty (FillingWitness T (CopyRule.after tree G) H) := by
  have binding := (DeepFilling.expand C L R cert).nullary_bindingFree none free closed
  obtain ⟨H,step,⟨w,_,_⟩⟩ := RetainedLocalTransfer.Copying.transport copyable tree
    (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free).1) (f.allLabels _ closed)
    (decoration C f cert avoid binding)
  have actual := step.rename (decorationIso C f cert avoid binding) (DeepIso.refl H)
  rw [decorationIso_host] at actual
  exact ⟨H,actual,⟨w⟩⟩
end Hypernets.Copying.NullaryResidual
