import Hypernets.Copying.PrimitiveThunkTransfer

/-! Complete allocation and assignment retained cases for the original
operational templates, including stable lambdas and instance-valued arguments.
No residual-admissibility or shallow-footprint premise is supplied by callers. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ForwardResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert free away leftClosed rightClosed

/-- All original stable arguments and their full output interfaces are retained; the concrete source and typed thunk barrier prove admissibility. -/
theorem allocation {O} (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_thunk_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.allocate G stable) f attached) free
    (BoxPermutation.PrimitiveFootprint.allocation G stable) (Allocation.before_bindingOrThunk G stable)
    (holeTermInputs C cert leftClosed) (Allocation.stable_allocation_safe G stable).1 (Allocation.stable_allocation_safe G stable).2 attached rfl
    (.local (.allocate G stable)) (template_outputClosed kind) leftClosed rightClosed Q P U step

/-- The reverse matching case uses the same original left occurrence; arbitrary right successors are quantified. -/
theorem allocation_converse {O} (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_thunk_converse_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.allocate G stable) f attached) free
    (BoxPermutation.PrimitiveFootprint.allocation G stable) (Allocation.before_bindingOrThunk G stable)
    (holeTermInputs C cert leftClosed) (Allocation.stable_allocation_safe G stable).1 (Allocation.stable_allocation_safe G stable).2 attached rfl
    (.local (.allocate G stable)) (template_outputClosed kind) leftClosed rightClosed Q P U step

/-- All original stable arguments and their full output interfaces are retained; the concrete source and typed thunk barrier prove admissibility. -/
theorem assignment {h O} (tree : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand L))
    (attached : f.ports (Assignment.inputPort h O 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_thunk_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.assign tree G stable) f attached) free
    (BoxPermutation.PrimitiveFootprint.assignment tree G stable) (Assignment.before_bindingOrThunk tree G stable)
    (holeTermInputs C cert leftClosed) (Assignment.stable_assignment_safe tree G stable).2.2.1 (Assignment.stable_assignment_safe tree G stable).2.2.2 attached rfl
    (.local (.assign tree G stable)) (template_outputClosed kind) leftClosed rightClosed Q P U step

/-- The reverse matching case uses the same original left occurrence; arbitrary right successors are quantified. -/
theorem assignment_converse {h O} (tree : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand L))
    (attached : f.ports (Assignment.inputPort h O 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_thunk_converse_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.assign tree G stable) f attached) free
    (BoxPermutation.PrimitiveFootprint.assignment tree G stable) (Assignment.before_bindingOrThunk tree G stable)
    (holeTermInputs C cert leftClosed) (Assignment.stable_assignment_safe tree G stable).2.2.1 (Assignment.stable_assignment_safe tree G stable).2.2.2 attached rfl
    (.local (.assign tree G stable)) (template_outputClosed kind) leftClosed rightClosed Q P U step

end Hypernets.Copying.OperationalTemplates.ForwardResidual
