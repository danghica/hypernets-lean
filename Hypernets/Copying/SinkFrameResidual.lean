import Hypernets.Copying.PointedFrameResidual
import Hypernets.Copying.BindingSinkRewrite
import Hypernets.Copying.FramedFillingTransfer

/-! Closed sink residuals give genuine binding-free whole-graph transfer,
including the exact local resume token and independently presented successors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined
variable {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J} {A : Hypernet d J []} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : BindingFree C)
    {X Y : Hypernet d J []} (w : FillingWitness T X Y)

include free

/-- Sink geometry discharges admissibility of the actual graft. No path or
binding-free premise remains on the computed frame or the assembled residual. -/
theorem sink_binding_quasi (localClosed : HoleFree w.context) (closed : T.OutputClosed)
    (left : HoleFree (afterGraph C f cert avoid L X))
    (right : HoleFree (afterGraph C f cert avoid R Y))
    (mode) (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term) (nonrewrite : mode ≠ .rewrite) :
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L X,
        (mode,afterPort C f cert avoid L X (w.leftPosition (mode,q)).2)⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R Y,
        (mode,afterPort C f cert avoid R Y (w.rightPosition (mode,q)).2)⟩) :=
  pointedResidual_binding_quasi C f cert avoid free.1 w
    (frame_plug_bindingFree_sink C f cert avoid w.context free w.free localClosed)
    closed left right mode q typed nonrewrite

/-- Two independently proved local steps produce two actual whole-graph
steps and an original binding-free residual specimen. All untouched shallow
and deep template occurrences remain in that specimen. -/
theorem sink_diamond {a : A.Vertex} {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L v)
    (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term)
    (leftStep : Rewrite A a X (w.leftPosition (.search,q)).2)
    (rightStep : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a)
      Y (w.rightPosition (.search,q)).2)
    (localClosed : HoleFree w.context) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L X)
      (afterPort C f cert avoid L X (w.leftPosition (.search,q)).2) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R v) (afterGraph C f cert avoid R Y)
      (afterPort C f cert avoid R Y (w.rightPosition (.search,q)).2) ∧
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L X,
        (.search,afterPort C f cert avoid L X (w.leftPosition (.search,q)).2)⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R Y,
        (.search,afterPort C f cert avoid R Y (w.rightPosition (.search,q)).2)⟩) := by
  have left : Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L X)
      (afterPort C f cert avoid L X (w.leftPosition (.search,q)).2) := by
    have h := left_rewrite C f cert avoid leftStep
    rw [attached] at h
    exact h
  have right := right_rewrite_at C f cert avoid attached rightStep
  exact ⟨left,right,sink_binding_quasi C f cert avoid free w localClosed closed
    (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed) .search q typed (by intro eq; cases eq)⟩

/-- The quantitative robustness clause holds for every independently
presented class successor of this matched sink case, with one step per side. -/
theorem sink_robust_case {a : A.Vertex} {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L v)
    (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term)
    (leftStep : Rewrite A a X (w.leftPosition (.search,q)).2)
    (rightStep : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a)
      Y (w.rightPosition (.search,q)).2)
    (localClosed : HoleFree w.context) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := sink_diamond C f cert avoid free w attached q typed
    leftStep rightStep localClosed closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

end Hypernets.Copying.RetainedFootprint
