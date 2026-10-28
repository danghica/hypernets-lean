import Hypernets.Copying.FullOperationalForwardRobustness
import Hypernets.Copying.ConverseRetainedResiduals
import Hypernets.Copying.ConverseCopyResidual
import Hypernets.Copying.ConverseStoreResiduals
import Hypernets.Copying.ConverseSameEquality
import Hypernets.Copying.ConverseDifferentEquality

/-! Universal converse robustness for both original operational templates:
actual right rewrites construct matching left rewrites and admissible residuals. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates
open Graph Combined
namespace ConverseResidual
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert free away leftClosed rightClosed rooted

/-- Exhaustive dispatch over the actual original nine local-rule constructors.
The rule's stability and copyability premises are retained without strengthening. -/
theorem local_case {J K} {A B : Hypernet d J K} {a b}
    (localStep : Local A a B b) (f : Opening.Occurrence A (C.expand R))
    (attached : f.ports a = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  cases localStep with
  | allocate G stable => exact allocation C cert free away leftClosed rightClosed rooted G stable f attached Q P U step
  | read T d => exact read C cert free away leftClosed rightClosed rooted T f attached Q P U step
  | assign T G stable => exact assignment C cert free away leftClosed rightClosed rooted T G stable f attached Q P U step
  | same T d => exact same C cert free away leftClosed rightClosed rooted T f attached Q P U step
  | different T U d => exact different C cert free away leftClosed rightClosed rooted T U f attached Q P _ step
  | unaryArithmetic d n => exact unary C cert free away leftClosed rightClosed rooted f attached Q P U step
  | binaryArithmetic o d m n => exact binary C cert free away leftClosed rightClosed rooted o f attached Q P U step
  | beta B G stable => exact beta C cert free away leftClosed rightClosed rooted B G stable f attached Q P U step
  | copy T G copyable => exact copying C cert free away leftClosed rightClosed T G copyable f attached Q P U step

/-- An arbitrary actual rewrite supplies its own complete local occurrence;
no rule match, footprint exclusion or finite-cut certificate is a premise. -/
theorem rewrite_case {H : Hypernet d [.term] []} {w}
    (actual : Rewrite (C.expand R) (Net.Expansion.host C R v) H w)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
  exact local_case C cert free away leftClosed rightClosed rooted localStep f attached Q P U step

/-- Reflection from any representation-class successor produces the exact
finite-allowance rewrite required by the exhaustive original-rule dispatch. -/
theorem class_step (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual => exact rewrite_case C cert free away leftClosed rightClosed rooted actual Q P U step
end ConverseResidual

/-- Full converse robustness of each original operational template. Original
specimen rootedness and binding freedom suffice; no operational law is assumed. -/
theorem template_robust_converse (kind : Kind) (Q P U : CostOrder) :
    (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Robust Q P U := by
  intro S _ leftRoot mode away successor next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  have rooted : Rooted ⟨S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    change StateClass.Rooted (StateClass.ofState S.leftState) at leftRoot
    rw [leftEq] at leftRoot
    exact leftRoot
  have remote : ¬ Search.Expansion.Entering S.context (.rewrite,S.token.2) := by
    change ¬ Search.Expansion.Entering S.context S.token at away
    have token : S.token = (.rewrite,S.token.2) := Prod.ext mode rfl
    rwa [token] at away
  change StateClass.machine.step (StateClass.ofState S.rightState) successor at next
  rw [rightEq] at next
  have result := ConverseResidual.class_step S.context S.edges S.allowed remote S.left_closed S.right_closed rooted Q P U next
  apply Or.inr
  change ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor a ∧
    StateClass.machine.Steps l (StateClass.ofState S.leftState) b ∧
    (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) a b
  rw [leftEq]
  exact result
end Hypernets.Copying.OperationalTemplates
