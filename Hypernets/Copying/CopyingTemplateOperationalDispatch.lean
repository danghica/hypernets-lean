import Hypernets.Copying.CopyingTemplateOperationalResiduals
import Hypernets.Copying.CopyingTemplateConverseOperational

/-! Exhaustive separation of the original operation and copying requests.
The non-copying part of both unrestricted robustness directions is discharged
for arbitrary actual representation-class successors, not chosen local steps. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined Search.Expansion

/-- Each original local rule is headed by an ordinary operation or by a term
contraction. These possibilities cover the unchanged complete operation set. -/
theorem local_head_cases {d I O} {G H : Hypernet d I O} {v w}
    (actual : Local G v H w) :
    (∃ e o, MatchEmbedding.HeadAt G v e (.operation o)) ∨
      ∃ e, MatchEmbedding.HeadAt G v e (.contraction .term) := by
  cases actual with
  | allocate G stable => exact .inl ⟨_,_,Allocation.head_at G⟩
  | read tree d => exact .inl ⟨_,_,(Dereference.localMatch tree d).head⟩
  | assign tree G stable => exact .inl ⟨_,_,(Assignment.localMatch tree G).head⟩
  | same tree d => exact .inl ⟨_,_,AtomEquality.Same.head_at tree d⟩
  | different tree other d => exact .inl ⟨_,_,AtomEquality.Different.head_at tree other d⟩
  | unaryArithmetic d n => exact .inl ⟨_,_,Arithmetic.unary_head d n⟩
  | binaryArithmetic op d m n => exact .inl ⟨_,_,Arithmetic.binary_head op d m n⟩
  | beta body G stable => exact .inl ⟨_,_,(Application.localMatch body G).head_at⟩
  | copy tree G copyable => exact .inr (CopyRule.before_active_head tree G ⟨0,by simp⟩)

/-- Every actual non-copying forward successor has a matching opposite step
and exact original residual, in the full unrestricted context class. -/
theorem forward_operational_step {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    (noncopy : ∀ e, ¬ MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) e (.contraction .term))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual =>
      obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
      rcases local_head_cases localStep with operational | ⟨e,copy⟩
      · exact ForwardResidual.operational_case C cert free leftClosed rightClosed away
          localStep f operational attached Q P U step
      · have mapped := f.matchEmbedding.head copy
        dsimp only [Opening.Occurrence.matchEmbedding] at mapped
        rw [attached] at mapped
        exact False.elim (noncopy _ mapped)

/-- Original left rootedness excludes the converse shallow operational
configurations. Actual non-copying right successors therefore satisfy the
full quantitative converse clause with no assumed matching footprint. -/
theorem converse_operational_step {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (noncopy : ∀ e, ¬ MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v) e (.contraction .term))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual =>
      obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
      rcases local_head_cases localStep with operational | ⟨e,copy⟩
      · exact ConverseResidual.operational_case C cert free leftClosed rightClosed away rooted
          localStep f operational attached Q P U step
      · have mapped := f.matchEmbedding.head copy
        dsimp only [Opening.Occurrence.matchEmbedding] at mapped
        rw [attached] at mapped
        exact False.elim (noncopy _ mapped)

end Hypernets.Copying.CopyingTemplate
