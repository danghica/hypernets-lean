import Hypernets.Copying.SinkFrameResidual

/-! Primitive retained footprints are rigid on the paired side. Closed sink
rules therefore have actual binding-free robustness, rather than a remaining
paired-local-step or residual-admissibility hypothesis. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined BoxPermutation
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (primitive : PrimitiveFootprint A)

include primitive

noncomputable def rightCopy (e : (skeleton C f cert avoid).Edge) :
    LabelCopy (rightFamily C f cert avoid e)
      ((R (f.edges e).1).edgeLabel (right C f.matchEmbedding cert avoid e).edge) :=
  (right C f.matchEmbedding cert avoid e).copy

theorem rightLabel (e : A.Edge) :
    LabelEquiv d ((R (f.edges e).1).edgeLabel (right C f.matchEmbedding cert avoid e).edge) (A.edgeLabel e) := by
  obtain ⟨p,label⟩ := primitive e
  have old := (reflect C f.matchEmbedding cert avoid).primitive e p label
  have paired := ((right C f.matchEmbedding cert avoid e).primitive p).mpr old
  change (R (f.edges e).1).edgeLabel (right C f.matchEmbedding cert avoid e).edge = primitiveLabel d p at paired
  rw [paired,label]
  exact labelEquiv_refl d _

/-- The actual right-filled primitive footprint is recursively isomorphic to
the original local source, without changing any local compute rule. -/
noncomputable def rightReconstruction : DeepIso
    ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) A where
  vertices := FillingCollapse.vertices _ _ _ (rightCopy C f cert avoid)
  edges := FillingCollapse.edges _ _ _ (rightCopy C f cert avoid)
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · exact False.elim ((rightCopy C f cert avoid e).no_internal v)
  edge_label x := by
    obtain ⟨e,x⟩ := x
    change LabelEquiv d ((R (f.edges e).1).edgeLabel x) (A.edgeLabel e)
    rw [(right C f.matchEmbedding cert avoid e).only x]
    exact rightLabel C f cert avoid primitive e
  source x := FillingCollapse.source _ _ _ (rightCopy C f cert avoid) x.1 x.2
  target x := FillingCollapse.target _ _ _ (rightCopy C f cert avoid) x.1 x.2

theorem rightReconstruction_inverse (a : A.Vertex) :
    Port.map (rightReconstruction C f cert avoid primitive).vertices.invFun a =
      Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a := by
  cases a <;> rfl

/-- Every actual rewrite on the primitive source has the same paired local
step; primitive rigidity establishes this premise rather than assuming it. -/
theorem primitive_right_step {B : Hypernet d J K} {a : A.Vertex} {b : B.Vertex}
    (step : Rewrite A a B b) :
    Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a) B b := by
  have result := step.rename (rightReconstruction C f cert avoid primitive).symm (DeepIso.refl B)
  have normalized : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Port.map (rightReconstruction C f cert avoid primitive).vertices.invFun a) B b := by
    simpa only [DeepIso.symm,Net.RelIso.symm,Bijection.symm,DeepIso.refl,Net.RelIso.refl,
      Bijection.refl,Port.map_id_fun,id_eq] using result
  exact Eq.mp (congrArg (fun v => Rewrite
    ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) v B b)
    (rightReconstruction_inverse C f cert avoid primitive a)) normalized

end Hypernets.Copying.RetainedFootprint

namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

theorem refl_leftPosition {d I O} (G : Hypernet d I O) (free : FocusFree G) (mode) (v : G.Vertex) :
    (refl (T := T) G free).leftPosition (mode,v) = (mode,v) := by cases v <;> rfl

theorem refl_rightPosition {d I O} (G : Hypernet d I O) (free : FocusFree G) (mode) (v : G.Vertex) :
    (refl (T := T) G free).rightPosition (mode,v) = (mode,v) := by cases v <;> rfl
end Hypernets.Copying.FillingWitness

namespace Hypernets.Copying.RetainedFootprint
open Graph Combined BoxPermutation
variable {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J} {A : Hypernet d J []} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : BindingFree C)
    (primitive : PrimitiveFootprint A)
    {B : Hypernet d J []} (focus : FocusFree B) (localClosed : HoleFree B)

include cert avoid free primitive focus localClosed

/-- A genuine original primitive sink rule gives a proved paired whole-graph
diamond and an original binding-free residual, preserving all unrelated fills. -/
theorem primitive_sink_diamond {a : A.Vertex} {b : B.Vertex} {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L v) (typed : B.vertexLabel b = .term)
    (localStep : Rewrite A a B b) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L B) (afterPort C f cert avoid L B b) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R v) (afterGraph C f cert avoid R B) (afterPort C f cert avoid R B b) ∧
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L B,(.search,afterPort C f cert avoid L B b)⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R B,(.search,afterPort C f cert avoid R B b)⟩) := by
  have result := sink_diamond C f cert avoid free (FillingWitness.refl B focus) attached b typed
    (by simpa only [FillingWitness.refl_leftPosition] using localStep)
    (by simpa only [FillingWitness.refl_rightPosition] using primitive_right_step C f cert avoid primitive localStep)
    localClosed closed leftClosed rightClosed
  simpa only [FillingWitness.refl_leftPosition,FillingWitness.refl_rightPosition] using result

/-- The full quantitative robustness clause for every primitive closed-sink
rewrite, with no assumed determinism, locality or paired-step law. -/
theorem primitive_sink_robust_case {a : A.Vertex} {b : B.Vertex} {v : C.Vertex}
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
  obtain ⟨left,right,residual⟩ := primitive_sink_diamond C f cert avoid free primitive focus localClosed
    attached typed localStep closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

/-- The same constructed diamond proves the converse quantitative case;
neither symmetry of the template relation nor a reversed filling is assumed. -/
theorem primitive_sink_converse_robust_case {a : A.Vertex} {b : B.Vertex} {v : C.Vertex}
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
  obtain ⟨left,right,residual⟩ := primitive_sink_diamond C f cert avoid free primitive focus localClosed
    attached typed localStep closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (FillingWitness.quasi_exchange _ residual) step

end Hypernets.Copying.RetainedFootprint
