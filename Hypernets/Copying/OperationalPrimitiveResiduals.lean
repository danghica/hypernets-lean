import Hypernets.Copying.ArithmeticResidualRobustness
import Hypernets.Copying.PrimitiveGuardedTransfer
import Hypernets.Copying.OperationalForwardOverlap

/-! Concrete forward operational-template robustness cases. These results
start from original complete left occurrences at a non-entering specimen
token; shallow-hole avoidance and admissible whole-graph residuals are proved. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ForwardResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert free away leftClosed rightClosed

/-- The unary arithmetic case needs no supplied footprint or residual law. -/
theorem unary {n} (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  Arithmetic.unary_retained_robust C cert free (template_outputClosed kind) leftClosed rightClosed f
    (ForwardOverlap.local_avoids C cert free away (.unaryArithmetic d n) f attached) attached Q P U step

/-- Both original binary arithmetic operations satisfy the concrete case. -/
theorem binary (o : Arithmetic.BinaryCode) {m n}
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  Arithmetic.binary_retained_robust C cert free (template_outputClosed kind) leftClosed rightClosed o f
    (ForwardOverlap.local_avoids C cert free away (.binaryArithmetic o d m n) f attached) attached Q P U step

/-- Reading retains the entire original atom-sharing tree and the store. The
stored contents stay attached through the original nonempty output interface. -/
theorem read {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand L))
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_guarded_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.read tree d) f attached) free
    (BoxPermutation.PrimitiveFootprint.dereference tree d) (Dereference.before_bindingGuarded tree d)
    (Dereference.focusFree_sides tree d).2 (Dereference.holeFree_sides tree d).2 attached rfl
    (.local (.read tree d)) (template_outputClosed kind) leftClosed rightClosed Q P U step

/-- The same-atom comparison branch keeps the complete original sharing tree. -/
theorem same {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand L))
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_guarded_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.same tree d) f attached) free
    (BoxPermutation.PrimitiveFootprint.same tree d) (AtomEquality.Same.before_bindingGuarded tree d)
    (AtomEquality.Same.focusFree_sides tree d).2 (AtomEquality.Same.holeFree_sides tree d).2 attached rfl
    (.local (.same tree d)) (template_outputClosed kind) leftClosed rightClosed Q P U step

/-- Distinct-atom comparison preserves both actual stores and both complete
sharing trees; it uses the original false-result compute rule. -/
theorem different {n m} (leftTree : ContractionTree .atom (n+1)) (rightTree : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (AtomEquality.Different.before leftTree rightTree d) (C.expand L))
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_guarded_robust_case C f cert
    (ForwardOverlap.local_avoids C cert free away (.different leftTree rightTree d) f attached) free
    (BoxPermutation.PrimitiveFootprint.different leftTree rightTree d)
    (AtomEquality.Different.before_bindingGuarded leftTree rightTree d)
    (AtomEquality.Different.focusFree_sides leftTree rightTree d).2
    (AtomEquality.Different.holeFree_sides leftTree rightTree d).2 attached rfl
    (.local (.different leftTree rightTree d)) (template_outputClosed kind) leftClosed rightClosed Q P U step

end Hypernets.Copying.OperationalTemplates.ForwardResidual
