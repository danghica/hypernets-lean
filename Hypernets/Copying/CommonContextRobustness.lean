import Hypernets.Copying.CommonContextPointed
import Hypernets.Copying.FramedFillingTransfer

/-! Actual paired common-context rewrites yield the paper's precise robust
case, with one transition on each side and the original recursive specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Combined
variable {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A C)
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    {X Y : Hypernet d J K} (w : FillingWitness T X Y)

include cert free

/-- Lift the proved local pair through its actual complete common-context cut.
The paired residual is constructed, with all unselected original fillings. -/
theorem diamond {a : A.Vertex}
    (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term)
    (leftStep : Rewrite ((skeleton C f).expand (localFamily C f L))
      (Net.Expansion.host (skeleton C f) (localFamily C f L) a)
      X (w.leftPosition (.search,q)).2)
    (rightStep : Rewrite ((skeleton C f).expand (localFamily C f R))
      (Net.Expansion.host (skeleton C f) (localFamily C f R) a)
      Y (w.rightPosition (.search,q)).2)
    (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L (f.ports a)) (afterGraph C f L X)
      (afterPort C f L X (w.leftPosition (.search,q)).2) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R (f.ports a)) (afterGraph C f R Y)
      (afterPort C f R Y (w.rightPosition (.search,q)).2) ∧
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f L X,
        (.search,afterPort C f L X (w.leftPosition (.search,q)).2)⟩)
      (StateClass.ofState ⟨d,afterGraph C f R Y,
        (.search,afterPort C f R Y (w.rightPosition (.search,q)).2)⟩) := by
  have left := rewrite_at C f L leftStep
  have right := rewrite_at C f R rightStep
  exact ⟨left,right,pointedResidual_quasi C f cert free w closed
    (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    .search q typed (by intro eq; cases eq)⟩

/-- The precise forward robustness clause holds for any independently
supplied successor of the actual left graph. -/
theorem robust_case {a : A.Vertex}
    (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term)
    (leftStep : Rewrite ((skeleton C f).expand (localFamily C f L))
      (Net.Expansion.host (skeleton C f) (localFamily C f L) a)
      X (w.leftPosition (.search,q)).2)
    (rightStep : Rewrite ((skeleton C f).expand (localFamily C f R))
      (Net.Expansion.host (skeleton C f) (localFamily C f R) a)
      Y (w.rightPosition (.search,q)).2)
    (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports a))⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports a))⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := diamond C f cert free w q typed
    leftStep rightStep closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

/-- The same genuine residual supplies the converse clause without reversing
or replacing the original template relation. -/
theorem converse_robust_case {a : A.Vertex}
    (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term)
    (leftStep : Rewrite ((skeleton C f).expand (localFamily C f L))
      (Net.Expansion.host (skeleton C f) (localFamily C f L) a)
      X (w.leftPosition (.search,q)).2)
    (rightStep : Rewrite ((skeleton C f).expand (localFamily C f R))
      (Net.Expansion.host (skeleton C f) (localFamily C f R) a)
      Y (w.rightPosition (.search,q)).2)
    (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports a))⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports a))⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨left,right,residual⟩ := diamond C f cert free w q typed
    leftStep rightStep closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left)))
    (FillingWitness.quasi_exchange _ residual) step

end Hypernets.Copying.CommonContextCut
