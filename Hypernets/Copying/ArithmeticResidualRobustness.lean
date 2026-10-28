import Hypernets.Copying.PrimitiveSinkTransfer

/-! Actual arithmetic cases of the paper's quantitative robustness clause.
The retained footprint and the original binding-free context determine the
whole-graph residual; no paired arithmetic step or admissibility is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph Combined RetainedFootprint
variable {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e) (free : BindingFree C)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))

include cert free closed leftClosed rightClosed

/-- Unary negation uses the agreed natural-number operation `0 - n` and the
unchanged original arithmetic machine rule. -/
theorem unary_retained_robust {n} (f : Opening.Occurrence (unaryBefore d n) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_sink_robust_case C f cert avoid free (BoxPermutation.PrimitiveFootprint.unary d n)
    (safe_number d (neg n)).1 (safe_number d (neg n)).2 attached rfl
    (.local (.unaryArithmetic d n)) closed leftClosed rightClosed Q P U step

/-- Both binary addition and truncated natural-number subtraction satisfy the
same actual whole-graph matching law, at every natural-number argument pair. -/
theorem binary_retained_robust (o : BinaryCode) {m n}
    (f : Opening.Occurrence (binaryBefore o d m n) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_sink_robust_case C f cert avoid free (BoxPermutation.PrimitiveFootprint.binary o d m n)
    (safe_number d (o.eval m n)).1 (safe_number d (o.eval m n)).2 attached rfl
    (.local (.binaryArithmetic o d m n)) closed leftClosed rightClosed Q P U step

/-- The same concrete unary diamond also supplies the converse case for an
arbitrary independently presented successor of the right-hand machine. -/
theorem unary_retained_converse_robust {n} (f : Opening.Occurrence (unaryBefore d n) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_sink_converse_robust_case C f cert avoid free (BoxPermutation.PrimitiveFootprint.unary d n)
    (safe_number d (neg n)).1 (safe_number d (neg n)).2 attached rfl
    (.local (.unaryArithmetic d n)) closed leftClosed rightClosed Q P U step

theorem binary_retained_converse_robust (o : BinaryCode) {m n}
    (f : Opening.Occurrence (binaryBefore o d m n) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_sink_converse_robust_case C f cert avoid free (BoxPermutation.PrimitiveFootprint.binary o d m n)
    (safe_number d (o.eval m n)).1 (safe_number d (o.eval m n)).2 attached rfl
    (.local (.binaryArithmetic o d m n)) closed leftClosed rightClosed Q P U step

end Hypernets.Copying.Arithmetic
