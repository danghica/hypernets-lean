import Hypernets.Copying.LambdaEntryAllocation
import Hypernets.Copying.LambdaEntryAssignment
import Hypernets.Copying.LambdaEntryStoreResiduals
import Hypernets.Copying.LambdaEntryNumericResiduals
import Hypernets.Copying.ConverseQuasiRelations

/-! Exhaustive actual-machine dispatch for all seven original rules other
than beta and copying. The two excluded heads are stated explicitly; this
is a proved part of parametricity robustness, not its universal conclusion. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined

/-- The original token is not an application or term-contraction head.
These are precisely the two local families handled by separate diagrams. -/
def NoncriticalHead {d I O} (G : Hypernet d I O) (v : G.Vertex) : Prop :=
  ∀ e, ¬ MatchEmbedding.HeadAt G v e (.operation .app) ∧
    ¬ MatchEmbedding.HeadAt G v e (.contraction .term)

variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (reverseHeads : T.converse.LambdaEntries) (none : T.NoOutputs)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (outputClosed : T.OutputClosed) {v : C.Vertex}
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))
    (noncritical : NoncriticalHead (C.expand L) (Net.Expansion.host C L v))
include cert heads reverseHeads none free leftClosed rightClosed outputClosed leftRoot rightRoot noncritical

/-- The unchanged nine-constructor local relation is dispatched exhaustively.
All seven permitted branches construct the matching step and residual; beta
and copying contradict the exact excluded original head labels. -/
theorem noncritical_local {J K} {A B : Hypernet d J K} {a b}
    (actual : Local A a B b) (f : Opening.Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  cases actual with
  | allocate G stable =>
    exact allocation_robust_case C cert free leftClosed rightClosed outputClosed heads
      G stable f attached leftRoot rightRoot Q P U step
  | read tree d =>
    exact read_robust_case C cert none free leftClosed rightClosed outputClosed heads
      tree f attached Q P U step
  | assign tree G stable =>
    exact assignment_robust_case C cert none free leftClosed rightClosed outputClosed heads
      reverseHeads tree G stable f attached rightRoot Q P U step
  | same tree d =>
    exact same_robust_case C cert none free leftClosed rightClosed outputClosed heads
      tree f attached Q P U step
  | different tree other d =>
    exact different_robust_case C cert none free leftClosed rightClosed outputClosed heads
      tree other f attached Q P U step
  | unaryArithmetic d n =>
    exact unary_robust_case C cert heads free leftClosed rightClosed outputClosed
      f attached Q P U step
  | binaryArithmetic o d m n =>
    exact binary_robust_case C cert heads free leftClosed rightClosed outputClosed
      o f attached Q P U step
  | beta body G stable =>
    have mapped := f.matchEmbedding.head (Application.localMatch body G).head_at
    change MatchEmbedding.HeadAt (C.expand L) (f.ports (.input 0)) _ (.operation .app) at mapped
    rw [attached] at mapped
    exact False.elim ((noncritical _).1 mapped)
  | copy tree G copyable =>
    obtain ⟨e,head⟩ := CopyRule.before_active_head tree G ⟨0,by simp⟩
    have mapped := f.matchEmbedding.head head
    change MatchEmbedding.HeadAt (C.expand L) (f.ports (.input ⟨0,by simp⟩)) _ (.contraction .term) at mapped
    rw [attached] at mapped
    exact False.elim ((noncritical _).2 mapped)

/-- Any supplied quotient-machine successor reflects to an actual original
local occurrence and is handled by the complete noncritical dispatch. -/
theorem noncritical_step (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual =>
      obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
      exact noncritical_local C cert heads reverseHeads none free leftClosed rightClosed outputClosed
        leftRoot rightRoot noncritical localStep f attached Q P U step

omit noncritical in
/-- Every actual opposite noncritical successor satisfies the clause in the
opposite of the original directed specimen system. No symmetry of the
template or auxiliary cost relations is assumed. -/
theorem noncritical_converse_step
    (rightNoncritical : NoncriticalHead (C.expand R) (Net.Expansion.host C R v))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨k,l,s,t,cost,left,right,residual⟩ :=
    noncritical_step C (fun e => (cert e).converse) reverseHeads heads none.converse
      free rightClosed leftClosed outputClosed.converse rightRoot leftRoot rightNoncritical Q P U step
  exact ⟨k,l,s,t,cost,left,right,Specimens.converse_quasi_rel outputClosed residual⟩

end Hypernets.Copying.LambdaEntryOverlap
