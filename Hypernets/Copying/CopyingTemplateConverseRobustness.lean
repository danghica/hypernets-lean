import Hypernets.Copying.CopyingConverseRetained
import Hypernets.Copying.CopyingNormalMatch
import Hypernets.Copying.CopyingRemoteRobustCase
import Hypernets.Copying.CopyingTemplateOperationalDispatch

/-! Full converse robustness of the original unrestricted copying template.
Actual right successors are classified into the eight operation cases,
retained selected copying spines, or a first original shallow copying input.
Every matching step and residual specimen is constructed by proved rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined Opening Search.Expansion
namespace ConverseResidual
variable {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
include cert free leftClosed rightClosed away

/-- Every actual right copying match is handled. The selected spine either
remains outside shallow replacements or enters one exact original hole; the
latter includes distinguished, positive, and final remaining inputs. -/
theorem copying_case {m k h} (T : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (f : Occurrence (CopyRule.before T H) (C.expand R))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨V,normal,g,input⟩ := CopyRule.normalized_occurrence T H copyable f
  have token := input.trans attached
  let matched := ((CopyRule.localSuccessorMatch T normal).map g).atToken token
  rcases RemoteRight.match_cases C cert rightClosed away matched with
    ⟨retained,cost,a,source,path,label,kind⟩ |
    ⟨hole,name,i,n,orientation,spine,holeLabel,atToken,atOutput,owners⟩
  · have last (name) : C.edgeLabel
        (g.edges (Serial.rightEdge (CopyRule.tree T d) V normal.head)).1 ≠ primitiveLabel d (.hole name) := by
      intro bad
      have impossible := primitiveLabel_injective d (label.symm.trans bad)
      rcases kind with kind | ⟨o,kind⟩ <;> rw [kind] at impossible <;> cases impossible
    obtain ⟨n,S,rematch,atInput,avoid⟩ := RemoteRight.retained_occurrence C cert rightClosed T normal g away token last
    exact retained_local_case C cert free leftClosed rightClosed (.copy S V normal.copyable)
      rematch avoid atInput Q P U step
  · obtain ⟨X,Y,x,y,left,right,⟨residual⟩⟩ := RemoteContext.any_hole_diagram
      C cert free leftClosed (ContractionSpine.tree .term n orientation) spine hole name holeLabel i atOutput
    rw [atToken] at left right
    exact residual.converse_matching_robust_case left right leftClosed Q P U step

/-- All nine original local rules, with their original stability/copyability
premises and full recursive bodies, satisfy the converse clause. -/
theorem local_case (rooted : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    {J K} {A B : Hypernet d J K} {a b}
    (actual : Local A a B b) (f : Occurrence A (C.expand R))
    (attached : f.ports a = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  cases actual with
  | allocate G stable =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.allocate G stable) f ⟨_,_,Allocation.head_at G⟩ attached Q P U step
  | read T d =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.read T d) f ⟨_,_,(Dereference.localMatch T d).head⟩ attached Q P U step
  | assign T G stable =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.assign T G stable) f ⟨_,_,(Assignment.localMatch T G).head⟩ attached Q P U step
  | same T d =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.same T d) f ⟨_,_,AtomEquality.Same.head_at T d⟩ attached Q P U step
  | different T S d =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.different T S d) f ⟨_,_,AtomEquality.Different.head_at T S d⟩ attached Q P U step
  | unaryArithmetic d n =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.unaryArithmetic d n) f ⟨_,_,Arithmetic.unary_head d n⟩ attached Q P U step
  | binaryArithmetic op d m n =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.binaryArithmetic op d m n) f ⟨_,_,Arithmetic.binary_head op d m n⟩ attached Q P U step
  | beta B G stable =>
    exact operational_case C cert free leftClosed rightClosed away rooted
      (.beta B G stable) f ⟨_,_,(Application.localMatch B G).head_at⟩ attached Q P U step
  | copy T G copyable => exact copying_case C cert free leftClosed rightClosed away T G copyable f attached Q P U step

/-- Every actual quotient-machine right successor supplies its own complete
local occurrence and receives the exhaustive actual converse diagram. -/
theorem class_step (rooted : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
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
      exact local_case C cert free leftClosed rightClosed away rooted localStep f attached Q P U step

end ConverseResidual

/-- Universal converse robustness of the unchanged copying family, in the
paper's unrestricted original context class. No matching, residual, locality,
or determinism hypothesis remains in this theorem. -/
theorem template_robust_converse (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust Q P U := by
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
  have remote : ¬ Entering S.context (.rewrite,S.token.2) := by
    change ¬ Entering S.context S.token at away
    have token : S.token = (.rewrite,S.token.2) := Prod.ext mode rfl
    rwa [token] at away
  change StateClass.machine.step (StateClass.ofState S.rightState) successor at next
  rw [rightEq] at next
  have result := ConverseResidual.class_step S.context S.edges S.free S.left_closed S.right_closed remote rooted Q P U next
  apply Or.inr
  change ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor a ∧
    StateClass.machine.Steps l (StateClass.ofState S.leftState) b ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) a b
  rw [leftEq]
  exact result
end Hypernets.Copying.CopyingTemplate
