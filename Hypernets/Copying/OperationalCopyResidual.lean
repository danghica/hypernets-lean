import Hypernets.Copying.OperationalDeepExtraction
import Hypernets.Copying.OperationalForwardOverlap

/-! Whole-graph copying residuals for arbitrary actual retained occurrences.
The deep body decomposition, common finite cut, paired copying transition and
binding-free residual context are all constructed from original certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined
namespace RetainedFootprint

/-- A local paired residual returning through an original input yields exact
whole-graph transitions and the original binding-free quasi-specimen. -/
theorem input_diamond {d J K} (C : Hypernet d [.term] []) {L R}
    {A X Y : Hypernet d J K} (f : Opening.Occurrence A (C.expand L)) {T : PreTemplate}
    (cert : ∀ e, DeepFillingEdge T C L R e) (avoid : AvoidsShallow C f.matchEmbedding)
    (free : FocusFree C) (i : Fin J.length) (typed : J[i] = .term)
    (leftLocal : Rewrite A (.input i) X (.input i))
    (rightLocal : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input i)) Y (.input i))
    (w : FillingWitness T X Y) (binding : BindingFree (residualGraft C f cert avoid w))
    {v} (attached : f.ports (.input i) = Net.Expansion.host C L v)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L X)
      (afterPort C f cert avoid L X (.input i)) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R v) (afterGraph C f cert avoid R Y)
      (afterPort C f cert avoid R Y (.input i)) ∧
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L X,(.search,afterPort C f cert avoid L X (.input i))⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R Y,(.search,afterPort C f cert avoid R Y (.input i))⟩) := by
  have left := left_rewrite C f cert avoid leftLocal
  rw [attached] at left
  have right := right_rewrite_at C f cert avoid attached rightLocal
  have residual := pointedResidual_binding_quasi C f cert avoid free w binding closed
    (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    .search (.input i) typed (by intro eq; cases eq)
  exact ⟨left,right,by
    simpa only [FillingWitness.leftPosition_input,FillingWitness.rightPosition_input] using residual⟩
end RetainedFootprint

namespace OperationalTemplates.ForwardResidual
open RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert free away leftClosed rightClosed

/-- An actual original copying occurrence gives a complete one-step residual
diamond, including arbitrary recursive payloads and any original sharing tree. -/
theorem copying_diamond {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    ∃ H K : Hypernet d [.term] [], ∃ a b,
      Rewrite (C.expand L) (Net.Expansion.host C L v) H a ∧
      Rewrite (C.expand R) (Net.Expansion.host C R v) K b ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi Eq Eq
        (StateClass.ofState ⟨d,H,(.search,a)⟩) (StateClass.ofState ⟨d,K,(.search,b)⟩) := by
  let avoid := ForwardOverlap.local_avoids C cert free away (.copy tree G copyable) f attached
  obtain ⟨H,step,⟨w,binding,shallow⟩⟩ := DeepExtraction.copying C cert free leftClosed tree G copyable f avoid
  have graft := residualGraft_binding_open_guarded C f cert avoid free (CopyRule.before_bindingGuarded tree copyable)
    w binding shallow
  obtain ⟨left,right,residual⟩ := input_diamond C f cert avoid free.1 ⟨0,by simp⟩ (List.getElem_replicate _)
    (.local (.copy tree G copyable)) step w graft attached (template_outputClosed kind) leftClosed rightClosed
  exact ⟨_,_,_,_,left,right,residual⟩

/-- Quantitative forward copying robustness for any independently represented
successor. No decomposition, locality law or residual admissibility is assumed. -/
theorem copying {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,K,a,b,left,right,residual⟩ := copying_diamond C cert free away leftClosed rightClosed tree G copyable f attached
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step
end OperationalTemplates.ForwardResidual
end Hypernets.Copying
