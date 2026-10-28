import Hypernets.Copying.ConverseDeepExtraction
import Hypernets.Copying.ConverseSpecimenTransfer
import Hypernets.Copying.ConversePrimitiveOverlap
import Hypernets.Copying.AllocationAssignmentResiduals

/-! Actual right arithmetic, allocation and beta occurrences yield original
opposite-system residuals. Their retained footprints and beta-cut admissibility
are derived from the original left search history, never supplied as premises. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert free away leftClosed rightClosed rooted

/-- Original unary arithmetic, with agreed natural subtraction negation. -/
theorem unary {n} (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  let avoid := ConverseOverlap.unary_avoids C cert away rooted n f attached
  obtain ⟨right,left,residual⟩ := primitive_sink_diamond C f (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.unary d n) (Arithmetic.safe_number d (Arithmetic.neg n)).1
    (Arithmetic.safe_number d (Arithmetic.neg n)).2 attached rfl (.local (.unaryArithmetic d n))
    (PreTemplate.OutputClosed.converse (template_outputClosed kind)) rightClosed leftClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (Specimens.converse_quasi (template_outputClosed kind) residual) step

/-- Both original binary arithmetic rules keep their actual numeric operands. -/
theorem binary (o : Arithmetic.BinaryCode) {m n}
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  let avoid := ConverseOverlap.binary_avoids C cert away rooted o m n f attached
  obtain ⟨right,left,residual⟩ := primitive_sink_diamond C f (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.binary o d m n) (Arithmetic.safe_number d (o.eval m n)).1
    (Arithmetic.safe_number d (o.eval m n)).2 attached rfl (.local (.binaryArithmetic o d m n))
    (PreTemplate.OutputClosed.converse (template_outputClosed kind)) rightClosed leftClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (Specimens.converse_quasi (template_outputClosed kind) residual) step

/-- Allocation retains every original stable operand, including stable
lambda and instance values with their complete nonempty output interfaces. -/
theorem allocation {O} (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  let avoid := ConverseOverlap.allocation_avoids C cert away rooted G stable f attached
  obtain ⟨right,left,residual⟩ := primitive_thunk_diamond C f (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.allocation G stable) (Allocation.before_bindingOrThunk G stable)
    (holeTermInputs C cert leftClosed) (Allocation.stable_allocation_safe G stable).1
    (Allocation.stable_allocation_safe G stable).2 attached rfl (.local (.allocate G stable))
    (PreTemplate.OutputClosed.converse (template_outputClosed kind)) rightClosed leftClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (Specimens.converse_quasi (template_outputClosed kind) residual) step
end Hypernets.Copying.OperationalTemplates.ConverseResidual

namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert free away leftClosed rightClosed rooted

/-- The actual right beta match constructs a paired left beta computation,
with arbitrary recursive body fillings and a proved original common-context cut. -/
theorem beta_diamond {k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ H K : Hypernet (d+1) [.term] [], ∃ a b,
      Rewrite (C.expand R) (Net.Expansion.host C R v) H a ∧
      Rewrite (C.expand L) (Net.Expansion.host C L v) K b ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi Eq Eq
        (StateClass.ofState ⟨d+1,H,(.search,a)⟩) (StateClass.ofState ⟨d+1,K,(.search,b)⟩) := by
  let avoid := ConverseOverlap.beta_avoids C cert away rooted B G stable f attached
  obtain ⟨H,step,⟨w,binding⟩⟩ := beta_local C cert free rightClosed B G stable f avoid
  have frameFree := beta_frame_binding C cert free leftClosed B G stable f avoid rooted attached
  have graft := residualGraft_binding_frame C f (fun e => (cert e).converse) avoid frameFree 0 w binding
  obtain ⟨right,left,residual⟩ := converse_input_diamond C f cert avoid free.1 0 rfl
    (.local (.beta B G stable)) step w graft attached (template_outputClosed kind) leftClosed rightClosed
  exact ⟨_,_,_,_,right,left,residual⟩

/-- Quantitative converse beta for every supplied actual right successor.
No left occurrence, footprint law or residual-admissibility premise remains. -/
theorem beta {k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,K,a,b,right,left,residual⟩ := beta_diamond C cert free away leftClosed rightClosed rooted B G stable f attached
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left))) residual step
end Hypernets.Copying.OperationalTemplates.ConverseResidual
