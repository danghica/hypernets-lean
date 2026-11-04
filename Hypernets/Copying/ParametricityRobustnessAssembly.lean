import Hypernets.Copying.ParametricityNoncriticalRobustness
import Hypernets.Copying.ParametricityCopyRobustness
import Hypernets.Copying.LambdaEntryBetaResiduals
import Hypernets.Copying.ParametricityPadding

/-! Assembly of the original nine-rule robustness dispatch. The explicitly
named shallow-beta interface is an internal proof obligation; this file does
not assert that the remaining shallow family cases have been discharged. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.RobustnessAssembly
open Graph Opening Combined LambdaEntryOverlap

abbrev ForwardClause {d} (C : Hypernet d [.term] []) {R} (v : C.Vertex)
    (U : CostOrder) (successor : StateClass) :=
  ∃ k l s t, CostOrder.improvement.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
    StateClass.machine.Steps l
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines CostOrder.improvement) (StateClass.machine.Refines U) s t

abbrev ConverseClause {d} (C : Hypernet d [.term] []) {L} (v : C.Vertex)
    (P : CostOrder) (successor : StateClass) :=
  ∃ k l s t, CostOrder.overhead.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
    StateClass.machine.Steps l
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines CostOrder.overhead) s t

/-- Precise remaining forward shallow-beta obligation, for the actual
selected original function and independently supplied whole-machine step. -/
def ShallowForward : Prop :=
  ∀ {d} (C : Hypernet (d+1) [.term] []) {L R}
    (_cert : ∀ e, DeepFillingEdge template C L R e), FocusFree C →
    HoleFree (C.expand L) → HoleFree (C.expand R) →
    ∀ {v : C.Vertex},
    Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v) →
    Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v) →
    ∀ {k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)}
      (a : Application.Match (C.expand L) (Net.Expansion.host C L v) B)
      (q : Hole), C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.hole q) →
    ∀ (U : CostOrder) {successor : StateClass},
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor →
      ForwardClause C (R := R) v U successor

/-- The opposite obligation starts from an actual right match and keeps the
original directed cost inequality; no symmetry of the family is assumed. -/
def ShallowConverse : Prop :=
  ∀ {d} (C : Hypernet (d+1) [.term] []) {L R}
    (_cert : ∀ e, DeepFillingEdge template C L R e), FocusFree C →
    HoleFree (C.expand L) → HoleFree (C.expand R) →
    ∀ {v : C.Vertex},
    Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v) →
    Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v) →
    ∀ {k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)}
      (a : Application.Match (C.expand R) (Net.Expansion.host C R v) B)
      (q : Hole), C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.hole q) →
    ∀ (P : CostOrder) {successor : StateClass},
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor →
      ConverseClause C (L := L) v P successor

/-- Internal assembly data. An unconditional robustness theorem must supply
both fields from actual shallow-family diagrams. -/
structure ShallowBetaCases : Prop where
  forward : ShallowForward
  converse : ShallowConverse

/-- A retained actual noncritical head rules out both exceptional labels by
the original unique-source incidence law. -/
theorem noncritical_of_head {d I O} {G : Hypernet d I O} {v e p}
    (head : MatchEmbedding.HeadAt G v e p)
    (application : p ≠ .operation .app) (copying : p ≠ .contraction .term) :
    NoncriticalHead G v := by
  intro f
  constructor
  · intro other;exact application (MatchEmbedding.head_unique head other).2
  · intro other;exact copying (MatchEmbedding.head_unique head other).2

variable (shallow : ShallowBetaCases)
    {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex}
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))

include cert free leftClosed rightClosed leftRoot rightRoot

theorem noncritical_left {J K} {A : Hypernet d J K} {a e p}
    (f : Occurrence A (C.expand L)) (attached : f.ports a = Net.Expansion.host C L v)
    (head : MatchEmbedding.HeadAt A a e p) (application : p ≠ .operation .app)
    (copying : p ≠ .contraction .term) (U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ForwardClause C (R := R) v U successor := by
  have mapped := f.matchEmbedding.head head
  change MatchEmbedding.HeadAt (C.expand L) (f.ports a) _ p at mapped
  rw [attached] at mapped
  exact noncritical_step C cert free leftClosed rightClosed leftRoot rightRoot
    (noncritical_of_head mapped application copying) .improvement .improvement U step

theorem noncritical_right {J K} {A : Hypernet d J K} {a e p}
    (f : Occurrence A (C.expand R)) (attached : f.ports a = Net.Expansion.host C R v)
    (head : MatchEmbedding.HeadAt A a e p) (application : p ≠ .operation .app)
    (copying : p ≠ .contraction .term) (P : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ConverseClause C (L := L) v P successor := by
  have mapped := f.matchEmbedding.head head
  change MatchEmbedding.HeadAt (C.expand R) (f.ports a) _ p at mapped
  rw [attached] at mapped
  exact noncritical_converse_step C cert free leftClosed rightClosed leftRoot rightRoot
    (noncritical_of_head mapped application copying) .overhead P .overhead step

include shallow
/-- Exhaustive forward dispatch on every original local constructor. Only
the named shallow-beta field remains to be instantiated externally. -/
theorem forward_local {J K} {A B : Hypernet d J K} {a b}
    (actual : Local A a B b) (f : Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v)
    (U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ForwardClause C (R := R) v U successor := by
  classical
  cases actual with
  | allocate G stable =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Allocation.head_at G) (by intro h;cases h) (by intro h;cases h) U step
  | read tree d =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Dereference.localMatch tree d).head (by intro h;cases h) (by intro h;cases h) U step
  | assign tree G stable =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Assignment.localMatch tree G).head (by intro h;cases h) (by intro h;cases h) U step
  | same tree d =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (AtomEquality.Same.head_at tree d) (by intro h;cases h) (by intro h;cases h) U step
  | different tree other d =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (AtomEquality.Different.head_at tree other d) (by intro h;cases h) (by intro h;cases h) U step
  | unaryArithmetic d n =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Arithmetic.unary_head d n) (by intro h;cases h) (by intro h;cases h) U step
  | binaryArithmetic o d m n =>
    exact noncritical_left C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Arithmetic.binary_head o d m n) (by intro h;cases h) (by intro h;cases h) U step
  | copy tree G copyable =>
    exact CopyResidual.forward_case C cert free leftClosed rightClosed tree G copyable f attached
      .improvement .improvement U step
  | beta body G stable =>
    have matched := (Application.localMatch body G).map f
    rw [attached] at matched
    by_cases inside : ∃ q, C.edgeLabel matched.lam.1 = primitiveLabel _ (.hole q)
    · obtain ⟨q,label⟩ := inside
      exact shallow.forward C cert free leftClosed rightClosed leftRoot rightRoot matched q label U step
    · exact beta_robust_case C cert free template_paddingClosed template_outputClosed
        leftClosed rightClosed leftRoot rightRoot template_lambdaEntries matched
        (by intro q h;exact inside ⟨q,h⟩) .improvement .improvement U step

/-- The converse dispatch uses the actual right source match independently;
no converse operational classification premise is left implicit. -/
theorem converse_local {J K} {A B : Hypernet d J K} {a b}
    (actual : Local A a B b) (f : Occurrence A (C.expand R))
    (attached : f.ports a = Net.Expansion.host C R v)
    (P : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ConverseClause C (L := L) v P successor := by
  classical
  cases actual with
  | allocate G stable =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Allocation.head_at G) (by intro h;cases h) (by intro h;cases h) P step
  | read tree d =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Dereference.localMatch tree d).head (by intro h;cases h) (by intro h;cases h) P step
  | assign tree G stable =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Assignment.localMatch tree G).head (by intro h;cases h) (by intro h;cases h) P step
  | same tree d =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (AtomEquality.Same.head_at tree d) (by intro h;cases h) (by intro h;cases h) P step
  | different tree other d =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (AtomEquality.Different.head_at tree other d) (by intro h;cases h) (by intro h;cases h) P step
  | unaryArithmetic d n =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Arithmetic.unary_head d n) (by intro h;cases h) (by intro h;cases h) P step
  | binaryArithmetic o d m n =>
    exact noncritical_right C cert free leftClosed rightClosed leftRoot rightRoot f attached
      (Arithmetic.binary_head o d m n) (by intro h;cases h) (by intro h;cases h) P step
  | copy tree G copyable =>
    exact CopyResidual.converse_case C cert free leftClosed rightClosed tree G copyable f attached
      .overhead P .overhead step
  | beta body G stable =>
    have matched := (Application.localMatch body G).map f
    rw [attached] at matched
    by_cases inside : ∃ q, C.edgeLabel matched.lam.1 = primitiveLabel _ (.hole q)
    · obtain ⟨q,label⟩ := inside
      exact shallow.converse C cert free leftClosed rightClosed leftRoot rightRoot matched q label P step
    · exact beta_converse_robust_case C cert free template_paddingClosed template_outputClosed
        leftClosed rightClosed leftRoot rightRoot converse_lambdaEntries matched
        (by intro q h;exact inside ⟨q,h⟩) .overhead P .overhead step

theorem forward_step (U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ForwardClause C (R := R) v U successor := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual =>
      obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
      exact forward_local shallow C cert free leftClosed rightClosed leftRoot rightRoot localStep f attached U step

theorem converse_step (P : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ConverseClause C (L := L) v P successor := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual =>
      obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
      exact converse_local shallow C cert free leftClosed rightClosed leftRoot rightRoot localStep f attached P step


omit cert free leftClosed rightClosed leftRoot rightRoot in
/-- Once the independently constructed shallow-beta diagrams are supplied,
all original specimens satisfy forward improvement robustness. -/
theorem robust_of_shallow (U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust
      .improvement .improvement U := by
  intro S leftRoot rightRoot mode _ successor next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  have lr : Rooted ⟨S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    change StateClass.Rooted (StateClass.ofState S.leftState) at leftRoot
    rwa [leftEq] at leftRoot
  have rr : Rooted ⟨S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    change StateClass.Rooted (StateClass.ofState S.rightState) at rightRoot
    rwa [rightEq] at rightRoot
  change StateClass.machine.step (StateClass.ofState S.leftState) successor at next
  rw [leftEq] at next
  have result := forward_step shallow S.context S.edges S.free S.left_closed S.right_closed lr rr U next
  apply Or.inr
  change ∃ k l s t, CostOrder.improvement.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
    StateClass.machine.Steps l (StateClass.ofState S.rightState) t ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines CostOrder.improvement) (StateClass.machine.Refines U) s t
  rw [rightEq]
  exact result

omit cert free leftClosed rightClosed leftRoot rightRoot in
/-- The actual converse dispatch yields the original reverse cost direction,
conditional only on the explicitly named shallow-beta diagrams. -/
theorem converse_robust_of_shallow (P : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust
      .overhead P .overhead := by
  intro S rightRoot leftRoot mode _ successor next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  have lr : Rooted ⟨S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    change StateClass.Rooted (StateClass.ofState S.leftState) at leftRoot
    rwa [leftEq] at leftRoot
  have rr : Rooted ⟨S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    change StateClass.Rooted (StateClass.ofState S.rightState) at rightRoot
    rwa [rightEq] at rightRoot
  change StateClass.machine.step (StateClass.ofState S.rightState) successor at next
  rw [rightEq] at next
  have result := converse_step shallow S.context S.edges S.free S.left_closed S.right_closed lr rr P next
  apply Or.inr
  change ∃ k l s t, CostOrder.overhead.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
    StateClass.machine.Steps l (StateClass.ofState S.leftState) t ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines CostOrder.overhead) s t
  rw [leftEq]
  exact result

end Hypernets.Copying.Parametricity.RobustnessAssembly
