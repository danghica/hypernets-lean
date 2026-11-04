import Hypernets.Copying.LambdaEntryNoncriticalDispatch

/-! The complete original-host robustness branches for the seven local
families other than beta and copying, specialized to literal Figure 20. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined LambdaEntryOverlap
variable {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex}
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))
include cert free leftClosed rightClosed leftRoot rightRoot

/-- Every actual original forward rewrite other than beta or copying has
an actual matching opposite step and an admissible original parametricity
residual. All template interface laws are proved internally. -/
theorem noncritical_step
    (noncritical : NoncriticalHead (C.expand L) (Net.Expansion.host C L v))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  LambdaEntryOverlap.noncritical_step C cert template_lambdaEntries converse_lambdaEntries
    template_noOutputs free leftClosed rightClosed template_outputClosed
    leftRoot rightRoot noncritical Q P U step

/-- The original opposite specimen system has the corresponding complete
seven-rule dispatch for independently supplied right successors. The
remaining beta and copying heads are explicitly excluded, not assumed solved. -/
theorem noncritical_converse_step
    (noncritical : NoncriticalHead (C.expand R) (Net.Expansion.host C R v))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  LambdaEntryOverlap.noncritical_converse_step C cert template_lambdaEntries converse_lambdaEntries
    template_noOutputs free leftClosed rightClosed template_outputClosed
    leftRoot rightRoot noncritical Q P U step

end Hypernets.Copying.Parametricity
