import Hypernets.Copying.RetainedBetaFrame
import Hypernets.Copying.LambdaEntryAssignmentOverlap

/-! A lambda-entry specimen has exactly two beta-frame cases: the selected
function lambda belongs to a shallow family, or its app/lambda/box frame is
entirely retained. Argument contributions are deliberately not classified as
part of this frame and may contain arbitrary shallow families. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Opening Search.Expansion MatchEmbedding
variable {T : PreTemplate} {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (closed : HoleFree (C.expand L))
    {k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)} {v : C.Vertex}
    (a : Application.Match (C.expand L) (Net.Expansion.host C L v) B)
include cert heads closed

/-- If the selected function lambda is retained, its actual thunk target
forces the selected box to be retained as well. No fact about the argument's
primitive head or membership in a shallow family is required. -/
theorem beta_frame_avoids
    (function : ∀ q, C.edgeLabel a.lam.1 ≠ primitiveLabel (d+1) (.hole q)) :
    RetainedFootprint.AvoidsShallow C (Application.RetainedFrame.occurrence B a).matchEmbedding := by
  obtain ⟨lambda,_⟩ := (cert a.lam.1).retained_of_not_hole function
  have thunkTarget : Port.internal a.thunkWire ∈ (C.expand L).target a.lam := by
    rw [a.lambda_target]; exact List.mem_cons_self
  obtain ⟨w,eq⟩ := lambda.target_origin thunkTarget
  have boxSource : Net.Expansion.host C L w ∈ (C.expand L).source a.boxEdge := by
    rw [eq,a.box_source]; exact List.mem_cons_self
  have boxNotLambda : (C.expand L).edgeLabel a.boxEdge ≠ primitiveLabel (d+1) (.operation .lam) := by
    intro label
    have related := a.box_label
    rw [label] at related
    exact related
  intro e
  cases e
  · change ∀ q, C.edgeLabel a.app.1 ≠ primitiveLabel (d+1) (.hole q)
    exact source_not_hole C cert heads closed a.head_at.2 (by
      rw [a.head_at.1]; intro eq; cases primitiveLabel_injective (d+1) eq)
  · exact function
  · exact source_not_hole C cert heads closed boxSource boxNotLambda

/-- Exhaustive classification of every actual opening match at an original
host token. The retained branch excludes only the three frame edges; it does
not assert or require retention of any stable argument edge. -/
theorem beta_frame_classification :
    (∃ q, C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.hole q)) ∨
      RetainedFootprint.AvoidsShallow C (Application.RetainedFrame.occurrence B a).matchEmbedding := by
  classical
  by_cases shallow : ∃ q, C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.hole q)
  · exact .inl shallow
  · exact .inr (beta_frame_avoids C cert heads closed a (by
      intro q eq; exact shallow ⟨q,eq⟩))
end Hypernets.Copying.LambdaEntryOverlap
