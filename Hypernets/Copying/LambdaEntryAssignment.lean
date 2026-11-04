import Hypernets.Copying.LambdaEntryAssignmentResidual
import Hypernets.Copying.ConverseSpecimenTransfer

/-! The complete assignment robustness case for closed-output lambda-entry
templates. Both actual stable values are admitted, including shallow-family
lambdas, and the residual retains the original template at every old hole. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoOutputs)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (outputClosed : T.OutputClosed)
include cert none free leftClosed rightClosed outputClosed

/-- Every original assignment occurrence has a one-step/one-step diagram
with a genuine original residual. The supplied full atom tree is retained;
rooted search supplies the other filling's own stable value. -/
theorem assignment_matching (heads : T.LambdaEntries) (reverseHeads : T.converse.LambdaEntries)
    {h K} (tree : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (Assignment.inputPort h K 0) = Net.Expansion.host C L v)
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v)) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  have left := f.rewrite (.local (.assign tree G stable))
  rw [attached] at left
  obtain ⟨H,w,right⟩ := assignment_opposite_enabled C cert heads none tree G f attached rightRoot
  have head := f.matchEmbedding.head (Assignment.localMatch tree G).head
  change MatchEmbedding.HeadAt (C.expand L) (f.ports (Assignment.inputPort h K 0))
    (f.edges (Assignment.localMatch tree G).headEdge) (.operation (.binary .assign)) at head
  rw [attached] at head
  obtain ⟨paired⟩ := assignment_successor_pointed C cert heads reverseHeads free
    (assignment_head C cert heads head) left right
  refine ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),?_⟩
  exact paired.quasi outputClosed (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    (rewrite_endpoints_term left).2

/-- Assignment satisfies the quantitative robustness clause for every
independently supplied actual successor, without a shallow-footprint premise. -/
theorem assignment_robust_case (heads : T.LambdaEntries) (reverseHeads : T.converse.LambdaEntries)
    {h K} (tree : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (Assignment.inputPort h K 0) = Net.Expansion.host C L v)
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,residual⟩ := assignment_matching C cert none free leftClosed rightClosed outputClosed
    heads reverseHeads tree G stable f attached rightRoot
  exact FillingWitness.matching_robust_case Q P U left right residual step

/-- The same construction proves the converse in the opposite original
specimen system; no symmetry assumption on the template is introduced. -/
theorem assignment_converse_robust_case (heads : T.LambdaEntries) (reverseHeads : T.converse.LambdaEntries)
    {h K} (tree : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (Assignment.inputPort h K 0) = Net.Expansion.host C R v)
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,right,left,residual⟩ := assignment_matching C (fun e => (cert e).converse) none.converse
    free rightClosed leftClosed outputClosed.converse reverseHeads heads tree G stable f attached leftRoot
  exact FillingWitness.matching_robust_case Q P U right left (Specimens.converse_quasi outputClosed residual) step

end Hypernets.Copying.LambdaEntryOverlap
