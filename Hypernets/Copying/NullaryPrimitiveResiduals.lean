import Hypernets.Copying.AllContextResiduals
import Hypernets.Copying.PrimitiveSinkTransfer
import Hypernets.Copying.RetainedLocalViews

/-! Primitive retained rewrites admit actual paired residuals in the original
unrestricted context class. Nullary-template footprint theorems discharge the
retention premise; no binding-free or guarded-output condition is necessary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined BoxPermutation
variable {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : FocusFree C)
    (primitive : PrimitiveFootprint A)
include cert avoid free primitive

/-- Primitive rigidity supplies the opposite local step. The target is
focus-free because it is the reduct of the actual focus-free matched source,
so the common residual uses the original local target without extra premises. -/
theorem primitive_allContexts_input_diamond {B : Hypernet d J K}
    (i : Fin J.length) (typed : J[i] = .term)
    (localStep : Rewrite A (.input i) B (.input i))
    {v} (attached : f.ports (.input i) = Net.Expansion.host C L v)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L B)
      (afterPort C f cert avoid L B (.input i)) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R v) (afterGraph C f cert avoid R B)
      (afterPort C f cert avoid R B (.input i)) ∧
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L B,
        (.search,afterPort C f cert avoid L B (.input i))⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R B,
        (.search,afterPort C f cert avoid R B (.input i))⟩) := by
  have original : FocusFree A := f.allLabels _
    ((DeepFilling.expand C L R cert).focusFree free).1
  have target : FocusFree B := rewrite_focusFree localStep original
  exact allContexts_input_diamond C f cert avoid free i typed localStep
    (primitive_right_step C f cert avoid primitive localStep)
    (FillingWitness.refl B target) attached closed leftClosed rightClosed

/-- The paired actual rewrites yield the full quantitative clause for any
supplied successor, with zero extra left steps and one opposite compute step. -/
theorem primitive_allContexts_robust_case {B : Hypernet d J K}
    (i : Fin J.length) (typed : J[i] = .term)
    (localStep : Rewrite A (.input i) B (.input i))
    {v} (attached : f.ports (.input i) = Net.Expansion.host C L v)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := primitive_allContexts_input_diamond C f cert avoid free primitive
    i typed localStep attached closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

/-- Exchanging the constructed actual rewrites yields the converse case in
the original opposite specimen system, without a symmetry premise on T. -/
theorem primitive_allContexts_converse_robust_case {B : Hypernet d J K}
    (i : Fin J.length) (typed : J[i] = .term)
    (localStep : Rewrite A (.input i) B (.input i))
    {v} (attached : f.ports (.input i) = Net.Expansion.host C L v)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := primitive_allContexts_input_diamond C f cert avoid free primitive
    i typed localStep attached closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (FillingWitness.quasi_exchange _ residual) step

end Hypernets.Copying.RetainedFootprint
