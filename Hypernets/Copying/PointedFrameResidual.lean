import Hypernets.Copying.PointedFillingTransport

/-! The grafted whole-graph residual retains its original common-context
geometry and the local witness's actual resume coordinate on both sides. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedFootprint
open Graph Combined
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : FocusFree C)
    {X Y : Hypernet d J K} (w : FillingWitness T X Y)

/-- Each untouched component uses its literal original context corolla. -/
noncomputable def originalComponents (e : (frame C f cert avoid).Edge) :
    FillingWitness T (afterFamily C f cert avoid L X e) (afterFamily C f cert avoid R Y e) :=
  match e with
  | none => w.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
  | some e => FillingWitness.originalEdge (cert e.val) free

noncomputable def pointedResidual :
    FillingWitness T (afterGraph C f cert avoid L X) (afterGraph C f cert avoid R Y) :=
  FillingWitness.expand (frame C f cert avoid) (originalComponents C f cert avoid free w)

/-- The geometric graft changes only the matched local common context. -/
noncomputable def residualGraft : Hypernet d I O :=
  (frame C f cert avoid).plug none
    (w.context.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)

theorem pointedResidual_context : (pointedResidual C f cert avoid free w).context =
    (frame C f cert avoid).expand (SingleExpansion.family (frame C f cert avoid) none
      (w.context.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)) := by
  apply congrArg (Net.expand (frame C f cert avoid))
  funext e
  cases e with
  | none =>
    simp only [originalComponents,SingleExpansion.selected]
    exact w.reboundary_context _ _
  | some e =>
    simp only [originalComponents,FillingWitness.originalEdge_context,SingleExpansion.family,
      dite_eq_right (Option.some_ne_none e)]
    rfl

/-- The assembled residual context is the actual finite cut with the local
common context plugged in. Original hole names and box bodies are preserved. -/
noncomputable def pointedResidual_contextIso :
    DeepIso (pointedResidual C f cert avoid free w).context (residualGraft C f cert avoid w) := by
  rw [pointedResidual_context]
  exact SingleExpansion.iso (frame C f cert avoid) none _

theorem pointedResidual_binding (binding : BindingFree (residualGraft C f cert avoid w)) :
    BindingFree (pointedResidual C f cert avoid free w).context :=
  (BindingFree.iso_iff (pointedResidual_contextIso C f cert avoid free w)).mpr binding

/-- Insert the local witness's exact common-context coordinate into the graft. -/
noncomputable def residualPoint (q : w.context.Vertex) :
    (pointedResidual C f cert avoid free w).context.Vertex :=
  Net.Expansion.insert (frame C f cert avoid)
    (fun e => (originalComponents C f cert avoid free w e).context) none
    (w.reboundaryVertex (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm q)

theorem residualPoint_left (mode) (q : w.context.Vertex) :
    (pointedResidual C f cert avoid free w).leftPosition (mode,residualPoint C f cert avoid free w q) =
      (mode,afterPort C f cert avoid L X (w.leftPosition (mode,q)).2) := by
  unfold pointedResidual residualPoint
  rw [FillingWitness.expand_selected_leftPosition]
  change (mode,Net.Expansion.insert (frame C f cert avoid) (afterFamily C f cert avoid L X) none ((w.reboundary _ _).leftPosition
    (mode,w.reboundaryVertex _ _ q)).2) = _
  rw [FillingWitness.reboundary_leftPosition]
  rfl

theorem residualPoint_right (mode) (q : w.context.Vertex) :
    (pointedResidual C f cert avoid free w).rightPosition (mode,residualPoint C f cert avoid free w q) =
      (mode,afterPort C f cert avoid R Y (w.rightPosition (mode,q)).2) := by
  unfold pointedResidual residualPoint
  rw [FillingWitness.expand_selected_rightPosition]
  change (mode,Net.Expansion.insert (frame C f cert avoid) (afterFamily C f cert avoid R Y) none ((w.reboundary _ _).rightPosition
    (mode,w.reboundaryVertex _ _ q)).2) = _
  rw [FillingWitness.reboundary_rightPosition]
  rfl

theorem residualPoint_label (q : w.context.Vertex) :
    (pointedResidual C f cert avoid free w).context.vertexLabel (residualPoint C f cert avoid free w q) =
      w.context.vertexLabel q := by
  exact (Net.Expansion.insert_label (frame C f cert avoid)
    (fun e => (originalComponents C f cert avoid free w e).context) none
    (w.reboundaryVertex (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm q)).trans
    (w.reboundaryVertex_label _ _ q)

end Hypernets.Copying.RetainedFootprint

namespace Hypernets.Copying.RetainedFootprint
open Graph Combined

/-- Once the explicit graft satisfies the paper's path restriction, its actual
paired resume positions form an original binding-free quasi-specimen. This
also covers resume points internal to the local common context. -/
theorem pointedResidual_binding_quasi {d} (C : Hypernet d [.term] [])
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (free : FocusFree C)
    {X Y : Hypernet d J K} (w : FillingWitness T X Y)
    (binding : BindingFree (residualGraft C f cert avoid w)) (closed : T.OutputClosed)
    (left : HoleFree (afterGraph C f cert avoid L X))
    (right : HoleFree (afterGraph C f cert avoid R Y))
    (mode) (q : w.context.Vertex) (typed : w.context.vertexLabel q = .term) (nonrewrite : mode ≠ .rewrite) :
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,afterGraph C f cert avoid L X,
        (mode,afterPort C f cert avoid L X (w.leftPosition (mode,q)).2)⟩)
      (StateClass.ofState ⟨d,afterGraph C f cert avoid R Y,
        (mode,afterPort C f cert avoid R Y (w.rightPosition (mode,q)).2)⟩) := by
  have result := (pointedResidual C f cert avoid free w).binding_quasi
    (pointedResidual_binding C f cert avoid free w binding) closed left right
    (mode,residualPoint C f cert avoid free w q)
    ((residualPoint_label C f cert avoid free w q).trans typed) nonrewrite
  simpa only [residualPoint_left,residualPoint_right] using result

end Hypernets.Copying.RetainedFootprint
