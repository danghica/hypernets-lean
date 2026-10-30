import Hypernets.Copying.LambdaEntryNumericOverlap

/-! Actual quantitative arithmetic branches for templates with lambda-value
entries, including both directions of the original parametricity template. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (outputClosed : T.OutputClosed)
include cert heads free leftClosed rightClosed outputClosed

/-- Every actual unary arithmetic successor has an opposite original
compute step and a genuine residual specimen, with one transition per side. -/
theorem unary_robust_case {n}
    (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  RetainedFootprint.primitive_allContexts_robust_case C f cert
    (unary_avoids C cert heads leftClosed f attached) free
    (BoxPermutation.PrimitiveFootprint.unary d n) 0 rfl (.local (.unaryArithmetic d n))
    attached outputClosed leftClosed rightClosed Q P U step

/-- Both binary arithmetic operations preserve a genuine original specimen
and its exact one-step comparison, for every actual represented successor. -/
theorem binary_robust_case (o : Arithmetic.BinaryCode) {m n}
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  RetainedFootprint.primitive_allContexts_robust_case C f cert
    (binary_avoids C cert heads leftClosed o f attached) free
    (BoxPermutation.PrimitiveFootprint.binary o d m n) 0 rfl (.local (.binaryArithmetic o d m n))
    attached outputClosed leftClosed rightClosed Q P U step

end Hypernets.Copying.LambdaEntryOverlap
