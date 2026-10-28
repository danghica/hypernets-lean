import Hypernets.Copying.NullaryTemplates

/-! Whole-graph pointed residuals in the unrestricted context class. The actual
common context and resumed token are constructed; no path restriction is imposed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined

/-- The original pointed graft is an admissible residual for all contexts. -/
theorem pointedResidual_allContexts_quasi {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : FocusFree C)
    {X Y : Hypernet d J K} (w : FillingWitness T X Y)
    (closed : T.OutputClosed)
    (left : HoleFree (afterGraph C f cert avoid L X))
    (right : HoleFree (afterGraph C f cert avoid R Y))
    (mode) (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term) (nonrewrite : mode ≠ .rewrite) :
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L X,
        (mode,afterPort C f cert avoid L X (w.leftPosition (mode,q)).2)⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R Y,
        (mode,afterPort C f cert avoid R Y (w.rightPosition (mode,q)).2)⟩) := by
  have result := (pointedResidual C f cert avoid free w).quasi closed left right
    (mode,residualPoint C f cert avoid free w q)
    ((residualPoint_label C f cert avoid free w q).trans typed) nonrewrite
  simpa only [residualPoint_left,residualPoint_right] using result


/-- A local paired residual returning through an original input yields exact
whole-graph transitions and the original unrestricted quasi-specimen. -/
theorem allContexts_input_diamond {d J K} (C : Hypernet d [.term] []) {L R}
    {A X Y : Hypernet d J K} (f : Opening.Occurrence A (C.expand L)) {T : PreTemplate}
    (cert : ∀ e, DeepFillingEdge T C L R e) (avoid : AvoidsShallow C f.matchEmbedding)
    (free : FocusFree C) (i : Fin J.length) (typed : J[i] = .term)
    (leftLocal : Rewrite A (.input i) X (.input i))
    (rightLocal : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) (.input i)) Y (.input i))
    (w : FillingWitness T X Y)
    {v} (attached : f.ports (.input i) = Net.Expansion.host C L v)
    (closed : T.OutputClosed) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R)) :
    Rewrite (C.expand L) (Net.Expansion.host C L v) (afterGraph C f cert avoid L X)
      (afterPort C f cert avoid L X (.input i)) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R v) (afterGraph C f cert avoid R Y)
      (afterPort C f cert avoid R Y (.input i)) ∧
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L X,(.search,afterPort C f cert avoid L X (.input i))⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R Y,(.search,afterPort C f cert avoid R Y (.input i))⟩) := by
  have left := left_rewrite C f cert avoid leftLocal
  rw [attached] at left
  have right := right_rewrite_at C f cert avoid attached rightLocal
  have residual := pointedResidual_allContexts_quasi C f cert avoid free w closed
    (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    .search (.input i) typed (by intro eq; cases eq)
  exact ⟨left,right,by
    simpa only [FillingWitness.leftPosition_input,FillingWitness.rightPosition_input] using residual⟩
end Hypernets.Copying.RetainedFootprint
