import Hypernets.Copying.SharingCopySelection

/-! The copying case of universal sharing-template robustness, extracted from
an arbitrary actual occurrence in the original recursively filled specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingResidual
open Graph Combined

/-- Original rootedness determines the actual first input of the complete
maximal component. No subtree exclusion, common cut, or residual is assumed. -/
theorem copying_matching {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (typed : C.vertexLabel v = .term)
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
    {n k h} (A : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before A G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    : ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  have reachable := SharingContext.reachable C cert trees (Search.rooted_reachable rooted) v rfl typed
  obtain ⟨S,labels,a,rest,selected,distinct,boundary,join⟩ :=
    MaximalSharing.copy_selection C cert trees A copyable f attached reachable
  have result := SharingCopyContext.copy_matching C cert trees copyable
    (MaximalSharing.copyPayload C A f) S labels a rest distinct boundary join free closed
    leftClosed rightClosed
  simpa only [selected] using result


/-- Original rootedness determines the actual first input of the complete
maximal component. No subtree exclusion, common cut, or residual is assumed. -/
theorem copying {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (typed : C.vertexLabel v = .term)
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
    {n k h} (A : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before A G) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have reachable := SharingContext.reachable C cert trees (Search.rooted_reachable rooted) v rfl typed
  obtain ⟨S,labels,a,rest,selected,distinct,boundary,join⟩ :=
    MaximalSharing.copy_selection C cert trees A copyable f attached reachable
  have result := SharingCopyContext.copy_robust_case C cert trees copyable
    (MaximalSharing.copyPayload C A f) S labels a rest distinct boundary join free closed
    leftClosed rightClosed Q P U (successor := successor) (by simpa only [selected] using step)
  simpa only [selected] using result

end Hypernets.Copying.SharingResidual
