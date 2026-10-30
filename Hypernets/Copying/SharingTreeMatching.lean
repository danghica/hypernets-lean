import Hypernets.Copying.SharingRetainedResiduals
import Hypernets.Copying.SharingCopyRobustness
import Hypernets.Copying.SharingReadRobustness
import Hypernets.Copying.SharingAssignmentRobustness
import Hypernets.Copying.SharingSameRobustness
import Hypernets.Copying.SharingDifferentRobustness
import Hypernets.Copying.SharingInputSafety

/-! Full matching of every original local and contextual rewrite for sharing
templates. Actual maximal components and original residuals are constructed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingResidual
open Graph Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (typed : C.vertexLabel v = .term)
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert trees padding free closed leftClosed rightClosed typed rooted

/-- Exhaust the original nine local rules, retaining their actual stability
and copyability premises. This includes arbitrary sharing trees and recursive
beta bodies; no chosen matching or residual certificate is a hypothesis. -/
theorem local_matching {J K} {A B : Hypernet d J K} {a b}
    (localStep : Local A a B b) (f : Opening.Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v) :
    ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  cases localStep with
  | allocate G stable => exact allocation_matching C cert trees free closed leftClosed rightClosed G stable f attached
  | read A d => exact MaximalSharing.read_matching C cert trees free closed leftClosed rightClosed A f attached
  | assign A G stable => exact MaximalSharing.assignment_matching C cert trees free closed leftClosed rightClosed A G stable f attached
  | same A d => exact MaximalSharing.same_matching C cert trees free closed leftClosed rightClosed A f attached
  | different A B d => exact MaximalSharing.different_matching C cert trees free closed leftClosed rightClosed A B f attached
  | unaryArithmetic d n => exact unary_matching C cert trees free closed leftClosed rightClosed f attached
  | binaryArithmetic o d m n => exact binary_matching C cert trees free closed leftClosed rightClosed o f attached
  | beta B G stable => exact beta_matching C cert trees padding free closed leftClosed rightClosed B G stable f attached
  | copy A G copyable => exact copying_matching C cert trees free closed leftClosed rightClosed typed rooted A G copyable f attached

/-- Any actual original contextual rewrite supplies its own complete local
occurrence. The full matching pair is obtained without changing that rewrite. -/
theorem rewrite_matching {H : Hypernet d [.term] []} {w}
    (actual : Rewrite (C.expand L) (Net.Expansion.host C L v) H w) :
    ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
  exact local_matching C cert trees padding free closed leftClosed rightClosed typed rooted localStep f attached

/-- Match an independently presented original successor, rather than the
particular local successor chosen during the maximal-component construction. -/
theorem step_matching {s : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s) :
    ∃ t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G search => exact False.elim (Search.no_rewrite search)
    | rewrite actual =>
      obtain ⟨x,y,left,right,residual⟩ :=
        rewrite_matching C cert trees padding free closed leftClosed rightClosed typed rooted actual
      have equal := StateClass.machine_deterministic left step
      exact ⟨y,right,equal ▸ residual⟩

end Hypernets.Copying.SharingResidual

namespace Hypernets.Copying
open Graph Combined

/-- Every padding-closed sharing template matches actual rewrites in both
directions, even at entered specimens. The converse constructs the actual
opposite-side maximal components and restores the original orientation. -/
theorem PreTemplate.SharingTrees.stepMatching {T : PreTemplate} (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (closed : T.OutputClosed) : T.StepMatching closed := by
  intro S leftRoot rightRoot mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  have rootedLeft : Rooted ⟨S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    rw [leftEq] at leftRoot
    exact leftRoot
  have rootedRight : Rooted ⟨S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    rw [rightEq] at rightRoot
    exact rightRoot
  constructor
  · intro s step
    rw [leftEq] at step
    obtain ⟨t,next,residual⟩ := SharingResidual.step_matching S.context S.edges trees padding S.free closed
      S.left_closed S.right_closed S.term rootedLeft step
    refine ⟨t,?_,residual⟩
    rwa [rightEq]
  · intro t step
    rw [rightEq] at step
    have reversePadding : T.converse.PaddingClosed := fun pair => padding pair
    obtain ⟨s,next,residual⟩ := SharingResidual.step_matching S.context (fun e => (S.edges e).converse)
      trees.converse reversePadding S.free closed.converse S.right_closed S.left_closed S.term rootedRight step
    have reverse := Specimens.converse_quasi closed residual
    refine ⟨s,?_,?_⟩
    · rwa [leftEq]
    · intro hs ht
      obtain ⟨D,mode,dr,dl,right,left⟩ := reverse ht hs
      exact ⟨D,mode,dl,dr,left.symm,right.symm⟩

/-- Full input safety, with exact paired entry costs and both possible stuck
requests handled, follows for every original sharing template. -/
theorem PreTemplate.SharingTrees.inputSafe {T : PreTemplate} (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (Q P : CostOrder) :
    (Specimens.system T Specimens.allContexts trees.outputClosed).InputSafe Q P :=
  (trees.stepMatching padding trees.outputClosed).inputSafe trees Q P

/-- Universal forward robustness in the paper's original all-context class. -/
theorem PreTemplate.SharingTrees.robust {T : PreTemplate} (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (Q P U : CostOrder) :
    (Specimens.system T Specimens.allContexts trees.outputClosed).Robust Q P U :=
  (trees.stepMatching padding trees.outputClosed).robust Q P U

/-- Universal converse robustness reconstructs every original matching rewrite
and its actual recursive specimen, rather than assuming a symmetric relation. -/
theorem PreTemplate.SharingTrees.robust_converse {T : PreTemplate} (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (Q P U : CostOrder) :
    (Specimens.system T Specimens.allContexts trees.outputClosed).opposite.Robust Q P U :=
  (trees.stepMatching padding trees.outputClosed).robust_converse Q P U

end Hypernets.Copying
