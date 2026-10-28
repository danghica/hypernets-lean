import Hypernets.Copying.OperationalDeepLocal
import Hypernets.Copying.CopySourceBindingGuards
import Hypernets.Copying.RetainedBindingGuards
import Hypernets.Copying.BindingOpenGuardedReplacement

/-! Extract genuine local residuals from arbitrary complete retained
occurrences in the original paired whole graphs. No framed local decomposition
is supplied: the original finite cut and deep edge certificates construct it. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined
namespace RetainedFootprint

/-- Copying may duplicate arbitrary recursively filled box bodies. Original
source guards protect all output attachments of its actual common-context graft. -/
theorem residualGraft_binding_open_guarded {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L)) {T : PreTemplate}
    (cert : ∀ e, DeepFillingEdge T C L R e) (avoid : AvoidsShallow C f.matchEmbedding)
    (free : BindingFree C) (guard : BindingGuardedOutputs A)
    {X Y : Hypernet d J K} (w : FillingWitness T X Y)
    (binding : BindingFree w.context) (shallow : ∀ e, ¬ HoleLabel d (w.context.edgeLabel e)) :
    BindingFree (residualGraft C f cert avoid w) :=
  CompleteMatchCut.bindingFree_replace_open_guarded
    (skeletonOccurrence C f cert avoid).matchEmbedding (skeletonOccurrence C f cert avoid).label
    w.context free (skeleton_bindingGuarded_full C f cert avoid guard) binding shallow
end RetainedFootprint

namespace OperationalTemplates.DeepExtraction
open RetainedFootprint
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    (closed : HoleFree (C.expand L))

/-- Arbitrary complete beta occurrences expose an actual paired beta rewrite
and a binding-free local residual, with no caller-provided box decomposition. -/
theorem beta {d I O k h K} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    (closed : HoleFree (C.expand L))
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input 0)) H (.input 0) ∧
      Nonempty {w : FillingWitness (template kind) (Application.after B G) H // BindingFree w.context} := by
  obtain ⟨H,step,w⟩ := DeepLocal.Beta.transport B G (decoration C f cert avoid free) stable
    (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free.1).1) (f.allLabels _ closed)
  have actual := step.rename (decorationIso C f cert avoid free) (DeepIso.refl H)
  rw [decorationIso_host] at actual
  exact ⟨H,actual,w⟩

include cert free closed

/-- Every original copyable payload admits the paired computation, retaining
the full sharing tree and an actual shallow-hole-free local residual context. -/
theorem copying {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input ⟨0,by simp⟩))
      H (.input ⟨0,by simp⟩) ∧
      Nonempty {w : FillingWitness (template kind) (CopyRule.after tree G) H //
        BindingFree w.context ∧ ∀ e, ¬ HoleLabel d (w.context.edgeLabel e)} := by
  obtain ⟨H,step,w⟩ := DeepLocal.Copying.transport copyable tree
    (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free.1).1) (f.allLabels _ closed)
    (decoration C f cert avoid free)
  have actual := step.rename (decorationIso C f cert avoid free) (DeepIso.refl H)
  rw [decorationIso_host] at actual
  exact ⟨H,actual,w⟩
end OperationalTemplates.DeepExtraction
end Hypernets.Copying
