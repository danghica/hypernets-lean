import Hypernets.Copying.CopyingTemplatePrimitiveOverlap
import Hypernets.Copying.CopyingTemplateBetaOverlap
import Hypernets.Copying.UnrestrictedDeepLocal
import Hypernets.Copying.NullaryPrimitiveResiduals

/-! Actual all-context residuals for every original operational rule in a
copying specimen. Beta retains arbitrary recursive bodies; primitive rules
retain complete store trees and the original stable operands. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ForwardResidual
open Graph Combined RetainedFootprint ForwardOverlap Search.Expansion

/-- A complete retained beta match opens the actual paired recursive body and
constructs its unrestricted residual specimen, with exactly one step per side. -/
theorem beta {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {k h K} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have avoid := beta_avoids C cert leftClosed B G stable f attached
  obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.beta_local C cert template_paddingClosed free B G stable f avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f cert avoid free 0 rfl
    (.local (.beta B G stable)) paired w attached template_outputClosed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

/-- Every primitive-headed local rule, including arbitrary beta bodies,
has an actual matching step and an exact original residual. No binding-free
hypothesis, remote-overlap certificate, or residual assumption is required. -/
theorem operational_case {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    {J K} {A B : Hypernet d J K} {a b}
    (localStep : Local A a B b) (f : Opening.Occurrence A (C.expand L))
    (operational : ∃ e o, MatchEmbedding.HeadAt A a e (.operation o))
    (attached : f.ports a = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  cases localStep with
  | allocate G stable =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (Allocation.head_at G) attached (allocation_cases G stable)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.allocation G stable) 0 rfl (.local (.allocate G stable))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | read tree d =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (Dereference.localMatch tree d).head attached (read_cases tree d)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.dereference tree d) ⟨0,by simp [Dereference.inputs]⟩ rfl (.local (.read tree d))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | assign tree G stable =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (Assignment.localMatch tree G).head attached (assignment_cases tree G stable)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.assignment tree G stable) ⟨0,by simp [Assignment.inputs]⟩ rfl (.local (.assign tree G stable))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | same tree d =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (AtomEquality.Same.head_at tree d) attached (same_cases tree d)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.same tree d) ⟨0,by simp [AtomEquality.Same.inputs]⟩ rfl (.local (.same tree d))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | different tree other d =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (AtomEquality.Different.head_at tree other d) attached (different_cases tree other d)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.different tree other d) ⟨0,by simp [AtomEquality.Different.inputs]⟩ rfl (.local (.different tree other d))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | unaryArithmetic d n =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (Arithmetic.unary_head d n) attached (unary_cases d n)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.unary d n) 0 rfl (.local (.unaryArithmetic d n))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | binaryArithmetic op d m n =>
    have avoid := primitive_avoids C cert leftClosed away f.matchEmbedding
      (Arithmetic.binary_head op d m n) attached (binary_cases op d m n)
    exact primitive_allContexts_robust_case C f cert avoid free
      (BoxPermutation.PrimitiveFootprint.binary op d m n) 0 rfl (.local (.binaryArithmetic op d m n))
      attached template_outputClosed leftClosed rightClosed Q P U step
  | beta body G stable => exact beta C cert free leftClosed rightClosed body G stable f attached Q P U step
  | copy tree G copyable =>
    obtain ⟨e,o,head⟩ := operational
    obtain ⟨e',contr⟩ := CopyRule.before_active_head tree G ⟨0,by simp⟩
    exact False.elim (by have bad := (MatchEmbedding.head_unique head contr).2; cases bad)

/-- If a copying footprint is wholly retained, arbitrary recursively related
payloads supply actual paired copy steps and their exact original specimen.
Only shallow copying overlaps lie outside this retained-footprint case. -/
theorem retained_copying {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {n k h} (tree : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (f : Opening.Occurrence (CopyRule.before tree G) (C.expand L))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.copying_local C cert free tree G copyable f avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f cert avoid free ⟨0,by simp⟩
    (List.getElem_replicate _) (.local (.copy tree G copyable)) paired w attached template_outputClosed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step
end Hypernets.Copying.CopyingTemplate.ForwardResidual
