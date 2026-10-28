import Hypernets.Copying.OperationalCopyResidual
import Hypernets.Copying.RootedCompleteCut
import Hypernets.Copying.BetaSourceBindingGuards

/-! Arbitrary rooted beta occurrences have admissible actual finite cuts.
Their deep body residual is then grafted into that exact common context; no
auxiliary host-admissibility or framed-decomposition premise is required. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined
namespace RetainedFootprint

/-- An original sourced cut admits an arbitrary binding-free local witness,
including shallow operational occurrences exposed by opening a box. -/
theorem residualGraft_binding_frame {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L)) {T : PreTemplate}
    (cert : ∀ e, DeepFillingEdge T C L R e) (avoid : AvoidsShallow C f.matchEmbedding)
    (free : BindingFree (frame C f cert avoid)) (i : Fin J.length)
    {X Y : Hypernet d J K} (w : FillingWitness T X Y) (binding : BindingFree w.context) :
    BindingFree (residualGraft C f cert avoid w) := by
  refine BindingFree.plugAt (.shallow (frame C f cert avoid) none) _ ?_ free ?_
  · constructor
    · exact ⟨⟨0,J,K⟩,rfl⟩
    · exact ⟨_,(CompleteMatchCut.mem_hole_source _ _).mpr ⟨i,rfl⟩⟩
  · rw [← FillingWitness.reboundary_context]
    exact w.reboundary_binding _ _ binding
end RetainedFootprint

namespace OperationalTemplates.ForwardResidual
open RetainedFootprint
variable {kind d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert free away leftClosed rightClosed rooted

omit away rightClosed in
/-- Rootedness supplies the missing geometric fact for box opening: no
binding ancestor can enter the fresh cut's actual single term input. -/
theorem beta_frame_binding {k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (avoid : AvoidsShallow C f.matchEmbedding) : BindingFree (frame C f cert avoid) := by
  apply CompleteMatchCut.bindingFree_cut
    (skeletonOccurrence C f cert avoid).matchEmbedding (skeletonOccurrence C f cert avoid).label
  · intro i
    have same : i = 0 := Fin.ext (by have := i.isLt; simp_all)
    subst i
    apply left_reachable_context C cert (Search.rooted_reachable rooted)
    · exact (host_port C f.matchEmbedding cert avoid (.input 0)).trans attached
    · exact (skeletonOccurrence C f cert avoid).matchEmbedding.vertexLabel
        (skeletonOccurrence C f cert avoid).label (.input 0)
  · intro i
    have same : i = 0 := Fin.ext (by have := i.isLt; simp_all)
    subst i
    rfl
  · exact skeleton_bindingOrThunk_full C f cert avoid (Application.before_bindingOrThunk B G stable)
  · exact holeTermInputs C cert leftClosed
  · exact free

/-- Every original complete beta occurrence at a rooted non-entering token
has an actual paired computation and a binding-free whole-graph residual. -/
theorem beta_diamond {k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    ∃ H K : Hypernet (d+1) [.term] [], ∃ a b,
      Rewrite (C.expand L) (Net.Expansion.host C L v) H a ∧
      Rewrite (C.expand R) (Net.Expansion.host C R v) K b ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi Eq Eq
        (StateClass.ofState ⟨d+1,H,(.search,a)⟩) (StateClass.ofState ⟨d+1,K,(.search,b)⟩) := by
  let avoid := ForwardOverlap.local_avoids C cert free away (.beta B G stable) f attached
  obtain ⟨H,step,⟨w,binding⟩⟩ := DeepExtraction.beta C cert free leftClosed B G stable f avoid
  have frameFree := beta_frame_binding C cert free leftClosed rooted B G stable f attached avoid
  have graft := residualGraft_binding_frame C f cert avoid frameFree 0 w binding
  obtain ⟨left,right,residual⟩ := input_diamond C f cert avoid free.1 0 rfl
    (.local (.beta B G stable)) step w graft attached (template_outputClosed kind) leftClosed rightClosed
  exact ⟨_,_,_,_,left,right,residual⟩

/-- Quantitative rooted beta robustness for an independently supplied machine
successor, retaining the original stable argument and full recursive body. -/
theorem beta {k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,K,a,b,left,right,residual⟩ := beta_diamond C cert free away leftClosed rightClosed rooted B G stable f attached
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step
end OperationalTemplates.ForwardResidual
end Hypernets.Copying
