import Hypernets.Copying.PrimitiveSinkTransfer
import Hypernets.Copying.BindingStoreRewrite

/-! Primitive rules whose outputs have original binding ancestors admit the
same exact whole-graph transfer as sinks, with their nonempty outputs intact. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined BoxPermutation
variable {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : BindingFree C)
    (primitive : PrimitiveFootprint A) (guard : BindingGuardedOutputs A)
    {B : Hypernet d J K} (focus : FocusFree B) (localClosed : HoleFree B)

include cert avoid free primitive guard focus localClosed

/-- The original binding ancestors protect every output attachment, so the
actual grafted residual is admissible without assuming that the cut is. -/
theorem primitive_guarded_diamond {a : A.Vertex} {b : B.Vertex} {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L v) (typed : B.vertexLabel b = .term)
    (localStep : Rewrite A a B b) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L B) (afterPort C f cert avoid L B b) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R v) (afterGraph C f cert avoid R B) (afterPort C f cert avoid R B b) ∧
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L B,(.search,afterPort C f cert avoid L B b)⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R B,(.search,afterPort C f cert avoid R B b)⟩) := by
  have left : Rewrite (C.expand L) (Net.Expansion.host C L v)
      (afterGraph C f cert avoid L B) (afterPort C f cert avoid L B b) := by
    have h := left_rewrite C f cert avoid localStep
    rw [attached] at h
    exact h
  have right := right_rewrite_at C f cert avoid attached
    (primitive_right_step C f cert avoid primitive localStep)
  have residual := pointedResidual_binding_quasi C f cert avoid free.1 (FillingWitness.refl B focus)
    (frame_plug_bindingFree_guarded C f cert avoid B free primitive guard focus localClosed)
    closed (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    .search b typed (by intro eq; cases eq)
  exact ⟨left,right,by
    simpa only [FillingWitness.refl_leftPosition,FillingWitness.refl_rightPosition] using residual⟩

theorem primitive_guarded_robust_case {a : A.Vertex} {b : B.Vertex} {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L v) (typed : B.vertexLabel b = .term)
    (localStep : Rewrite A a B b) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := primitive_guarded_diamond C f cert avoid free primitive guard focus localClosed
    attached typed localStep closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

theorem primitive_guarded_converse_robust_case {a : A.Vertex} {b : B.Vertex} {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L v) (typed : B.vertexLabel b = .term)
    (localStep : Rewrite A a B b) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := primitive_guarded_diamond C f cert avoid free primitive guard focus localClosed
    attached typed localStep closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (FillingWitness.quasi_exchange _ residual) step

end Hypernets.Copying.RetainedFootprint
