import Hypernets.Copying.CopyingTemplateOperationalDispatch
import Hypernets.Copying.CopyingNormalMatch
import Hypernets.Copying.CopyingRemoteRobustCase

/-! Universal forward robustness of the original Figure 17 copying template.
All original operational rules, retained copying footprints and first shallow
copying entries are covered in arbitrary recursive unrestricted contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Opening Combined Search.Expansion
namespace ForwardResidual
variable {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))

include cert free leftClosed rightClosed away in
/-- An arbitrary actual copying occurrence is classified by its selected
resolution path. Retained payloads use a proved minimal original spine;
first shallow entries use the complete original prefix-and-hole diagram. -/
theorem copying_case {m k h} (tree : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (f : Occurrence (CopyRule.before tree H) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨V,normal,g,same⟩ := CopyRule.normalized_occurrence tree H copyable f
  have token := same.trans attached
  let matched := ((CopyRule.localSuccessorMatch tree normal).map g).atToken token
  rcases Remote.match_cases C cert leftClosed away matched with retained | shallow
  · obtain ⟨_,n,a,source,path,label,kind⟩ := retained
    have last : ∀ name, C.edgeLabel (g.edges (Serial.rightEdge (CopyRule.tree tree d) V normal.head)).1 ≠
        primitiveLabel d (.hole name) := by
      intro name bad
      have eq := primitiveLabel_injective d (label.symm.trans bad)
      rcases kind with e | ⟨o,e⟩ <;> rw [e] at eq <;> cases eq
    obtain ⟨n,T,occ,atHost,avoid⟩ := Remote.retained_occurrence C cert leftClosed tree normal g away token last
    exact retained_copying C cert free leftClosed rightClosed T V normal.copyable occ avoid atHost Q P U step
  · obtain ⟨hole,name,i,n,orientation,spine,label,atHost,link,_⟩ := shallow
    obtain ⟨X,Y,x,y,left,right,⟨residual⟩⟩ := RemoteContext.any_hole_diagram C cert free leftClosed
      (ContractionSpine.tree .term n orientation) spine hole name label i link
    rw [atHost] at left right
    exact residual.matching_robust_case left right leftClosed Q P U step

include cert free leftClosed rightClosed away in
/-- Exhaustive dispatch on the unchanged original nine local constructors.
Stability and copyability are precisely the original rule premises. -/
theorem local_case {J K} {A B : Hypernet d J K} {a b}
    (actual : Local A a B b) (f : Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  rcases local_head_cases actual with operational | ⟨e,head⟩
  · exact operational_case C cert free leftClosed rightClosed away actual f operational attached Q P U step
  · cases actual with
    | copy tree H copyable => exact copying_case C cert free leftClosed rightClosed away tree H copyable f attached Q P U step
    | allocate H stable => have bad := (MatchEmbedding.head_unique head (Allocation.head_at H)).2; cases bad
    | read tree d => have bad := (MatchEmbedding.head_unique head (Dereference.localMatch tree d).head).2; cases bad
    | assign tree H stable => have bad := (MatchEmbedding.head_unique head (Assignment.localMatch tree H).head).2; cases bad
    | same tree d => have bad := (MatchEmbedding.head_unique head (AtomEquality.Same.head_at tree d)).2; cases bad
    | different tree other d => have bad := (MatchEmbedding.head_unique head (AtomEquality.Different.head_at tree other d)).2; cases bad
    | unaryArithmetic d n => have bad := (MatchEmbedding.head_unique head (Arithmetic.unary_head d n)).2; cases bad
    | binaryArithmetic op d n m => have bad := (MatchEmbedding.head_unique head (Arithmetic.binary_head op d n m)).2; cases bad
    | beta B G stable => have bad := (MatchEmbedding.head_unique head (Application.localMatch B G).head_at).2; cases bad

include cert free leftClosed rightClosed away in
/-- The supplied quotient-machine step yields its own actual original local
occurrence; no deterministic matching or successor existence is assumed. -/
theorem class_step (Q P U : CostOrder) {successor}
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
      exact local_case C cert free leftClosed rightClosed away localStep f attached Q P U step
end ForwardResidual

/-- Full forward robustness of the original copying template in every
unrestricted recursive context, for the entire original copying UAM. -/
theorem template_robust (Q P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust Q P U := by
  intro S _ _ mode away successor next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  have remote : ¬ Entering S.context (.rewrite,S.token.2) := by
    change ¬ Entering S.context S.token at away
    have token : S.token = (.rewrite,S.token.2) := Prod.ext mode rfl
    rwa [token] at away
  change StateClass.machine.step (StateClass.ofState S.leftState) successor at next
  rw [leftEq] at next
  have result := ForwardResidual.class_step S.context S.edges S.free S.left_closed S.right_closed remote Q P U next
  apply Or.inr
  change ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
    StateClass.machine.Steps l (StateClass.ofState S.rightState) t ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t
  rw [rightEq]
  exact result

end Hypernets.Copying.CopyingTemplate
