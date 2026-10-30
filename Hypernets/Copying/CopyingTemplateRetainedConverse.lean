import Hypernets.Copying.CopyingTemplateLaws
import Hypernets.Copying.UnrestrictedDeepLocal
import Hypernets.Copying.NullaryRobustness

/-! Converse matching for a wholly retained original local footprint. This
constructs the actual opposite rewrite and unrestricted residual; the source
classification that discharges retention is a separate geometric argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ConverseResidual
open Graph Combined RetainedFootprint

/-- All nine original rules transport through a retained right source. Deep
bodies use original copying certificates in the reverse direction, preserving
all stability, copyability, padding, and recursive-interface requirements. -/
theorem retained_local_case {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {J K} {A B : Hypernet d J K} {a b}
    (localStep : Local A a B b) (f : Opening.Occurrence A (C.expand R))
    (avoid : AvoidsShallow C f.matchEmbedding) {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have reversed := fun e => (cert e).converse
  have close : template.converse.OutputClosed := template_outputClosed.converse
  have primitiveCase {J K} {A B : Hypernet d J K}
      (f : Opening.Occurrence A (C.expand R))
      (avoid : AvoidsShallow C f.matchEmbedding)
      (primitive : BoxPermutation.PrimitiveFootprint A)
      (i : Fin J.length) (typed : J[i] = .term)
      (actual : Rewrite A (.input i) B (.input i))
      (attached : f.ports (.input i) = Net.Expansion.host C R v) :
      ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
        StateClass.machine.Steps l
          (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
        (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
          (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
    obtain ⟨k,l,s,t,cost,ls,rs,residual⟩ := primitive_allContexts_robust_case C f reversed avoid free
      primitive i typed actual attached close rightClosed leftClosed Q P U step
    exact ⟨k,l,s,t,cost,ls,rs,Specimens.converse_quasi_rel template_outputClosed residual⟩
  cases localStep with
  | allocate G stable =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.allocation G stable) 0 rfl (.local (.allocate G stable)) attached
  | read tree d =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.dereference tree d) ⟨0,by simp [Dereference.inputs]⟩ rfl (.local (.read tree d)) attached
  | assign tree G stable =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.assignment tree G stable) ⟨0,by simp [Assignment.inputs]⟩ rfl (.local (.assign tree G stable)) attached
  | same tree d =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.same tree d) ⟨0,by simp [AtomEquality.Same.inputs]⟩ rfl (.local (.same tree d)) attached
  | different tree other d =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.different tree other d) ⟨0,by simp [AtomEquality.Different.inputs]⟩ rfl
        (.local (.different tree other d)) attached
  | unaryArithmetic d n =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.unary d n) 0 rfl (.local (.unaryArithmetic d n)) attached
  | binaryArithmetic op d m n =>
    exact primitiveCase f avoid
      (BoxPermutation.PrimitiveFootprint.binary op d m n) 0 rfl (.local (.binaryArithmetic op d m n)) attached
  | beta body G stable =>
    have padding : template.converse.PaddingClosed := fun pair => template_paddingClosed pair
    obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.beta_local C reversed padding free body G stable f avoid
    obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f reversed avoid free 0 rfl
      (.local (.beta body G stable)) paired w attached close rightClosed leftClosed
    exact FillingWitness.matching_robust_case Q P U
      (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right)))
      (Specimens.converse_quasi_rel template_outputClosed residual) step
  | copy tree G copyable =>
    obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.copying_local C reversed free tree G copyable f avoid
    obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f reversed avoid free ⟨0,by simp⟩
      (List.getElem_replicate _) (.local (.copy tree G copyable)) paired w attached close rightClosed leftClosed
    exact FillingWitness.matching_robust_case Q P U
      (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right)))
      (Specimens.converse_quasi_rel template_outputClosed residual) step

end Hypernets.Copying.CopyingTemplate.ConverseResidual
