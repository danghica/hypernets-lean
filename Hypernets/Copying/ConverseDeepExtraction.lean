import Hypernets.Copying.GenericRetainedLocal
import Hypernets.Copying.OperationalBetaResidual
import Hypernets.Copying.ConverseBetaOverlap

/-! Paired local rewrites extracted from actual right occurrences. Reversing
certificates changes neither machine rule nor common context. Rootedness is
always that of the original left graph, including in the beta cut proof. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

theorem PreTemplate.PaddingClosed.converse {T : PreTemplate} (padding : T.PaddingClosed) :
    T.converse.PaddingClosed := fun pair => padding pair

namespace OperationalTemplates.ConverseResidual
open RetainedFootprint
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    (rightClosed : HoleFree (C.expand R))
include cert free rightClosed

/-- All original copyable constructors are matched on the other side of an
actual retained right footprint; arbitrary boxed bodies remain recursively paired. -/
theorem copying_local {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand R))
    (avoid : AvoidsShallow C f.matchEmbedding) :
    ∃ H, Rewrite ((skeleton C f (fun e => (cert e).converse) avoid).expand
        (rightFamily C f (fun e => (cert e).converse) avoid))
      (Net.Expansion.host (skeleton C f (fun e => (cert e).converse) avoid)
        (rightFamily C f (fun e => (cert e).converse) avoid) (.input ⟨0,by simp⟩)) H (.input ⟨0,by simp⟩) ∧
      Nonempty {w : FillingWitness (template kind).converse (CopyRule.after tree G) H //
        BindingFree w.context ∧ ∀ e, ¬ HoleLabel d (w.context.edgeLabel e)} := by
  let rev := fun e => (cert e).converse
  obtain ⟨H,step,w⟩ := RetainedLocalTransfer.Copying.transport copyable tree
    (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free.1).2) (f.allLabels _ rightClosed)
    (decoration C f rev avoid free)
  have actual := step.rename (decorationIso C f rev avoid free) (DeepIso.refl H)
  rw [decorationIso_host] at actual
  exact ⟨H,actual,w⟩
end OperationalTemplates.ConverseResidual

namespace OperationalTemplates.ConverseResidual
open RetainedFootprint
variable {kind d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {k h K} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand R))
    (avoid : AvoidsShallow C f.matchEmbedding)
include cert free rightClosed stable

/-- Genuine reverse local beta extraction, using the proved padding law of
the original family and its reversal. The stable argument stays unchanged. -/
theorem beta_local :
    ∃ H, Rewrite ((skeleton C f (fun e => (cert e).converse) avoid).expand
        (rightFamily C f (fun e => (cert e).converse) avoid))
      (Net.Expansion.host (skeleton C f (fun e => (cert e).converse) avoid)
        (rightFamily C f (fun e => (cert e).converse) avoid) (.input 0)) H (.input 0) ∧
      Nonempty {w : FillingWitness (template kind).converse (Application.after B G) H // BindingFree w.context} := by
  let rev := fun e => (cert e).converse
  obtain ⟨H,step,w⟩ := RetainedLocalTransfer.Beta.transport B G (decoration C f rev avoid free)
    (PreTemplate.PaddingClosed.converse (template_paddingClosed kind)) stable
    (f.allLabels _ ((DeepFilling.expand C L R cert).focusFree free.1).2) (f.allLabels _ rightClosed)
  have actual := step.rename (decorationIso C f rev avoid free) (DeepIso.refl H)
  rw [decorationIso_host] at actual
  exact ⟨H,actual,w⟩

include leftClosed

omit rightClosed in
/-- The actual right match determines the cut geometry. Original left
rootedness, reflected to its common coordinate, proves that cut admissible. -/
theorem beta_frame_binding {input v}
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    BindingFree (frame C f (fun e => (cert e).converse) avoid) := by
  let rev := fun e => (cert e).converse
  let selected := skeletonOccurrence C f rev avoid
  have point : selected.ports (.input 0) = v := Net.Expansion.host_injective C R
    ((host_port C f.matchEmbedding rev avoid (.input 0)).trans attached)
  have typed : C.vertexLabel v = .term := by
    have value := selected.matchEmbedding.vertexLabel selected.label (.input 0)
    change C.vertexLabel (selected.ports (.input 0)) = .term at value
    rw [point] at value
    exact value
  apply CompleteMatchCut.bindingFree_cut selected.matchEmbedding selected.label
  · intro i
    have same : i = 0 := Fin.ext (by have := i.isLt; simp_all)
    subst i
    change Search.OperationReachable C (selected.ports (.input 0))
    rw [point]
    exact left_reachable_context C cert (Search.rooted_reachable rooted) v rfl typed
  · intro i
    have same : i = 0 := Fin.ext (by have := i.isLt; simp_all)
    subst i
    rfl
  · exact skeleton_bindingOrThunk_full C f rev avoid (Application.before_bindingOrThunk B G stable)
  · exact holeTermInputs C cert leftClosed
  · exact free
end OperationalTemplates.ConverseResidual
end Hypernets.Copying
