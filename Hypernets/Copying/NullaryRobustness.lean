import Hypernets.Copying.NullaryPrimitiveOverlap
import Hypernets.Copying.NullaryPrimitiveResiduals
import Hypernets.Copying.NullaryStoreFootprint
import Hypernets.Copying.NullaryDeepResiduals

/-! Full robustness of padding-closed nullary templates in unrestricted original
contexts. Every local rule supplies actual matching rewrites and residuals. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace NullaryResidual
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs) (padding : T.PaddingClosed)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex}
include cert none padding free leftClosed rightClosed

/-- Exhaust all nine original local rules, retaining their unchanged stability
and copyability hypotheses. Selected subtrees are constructed inside the proof. -/
theorem local_case {J K} {A B : Hypernet d J K} {a b}
    (localStep : Local A a B b) (f : Opening.Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts none.outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  cases localStep with
  | allocate G stable =>
    exact RetainedFootprint.primitive_allContexts_robust_case C f cert
      (NullaryOverlap.allocation_avoids C cert none leftClosed G stable f attached) free
      (BoxPermutation.PrimitiveFootprint.allocation G stable) 0 rfl (.local (.allocate G stable))
      attached none.outputClosed leftClosed rightClosed Q P U step
  | read tree d =>
    obtain ⟨m,tree,g,token,avoid⟩ := NullaryOverlap.read_occurrence C cert none leftClosed tree f attached
    exact RetainedFootprint.primitive_allContexts_robust_case C g cert avoid free
      (BoxPermutation.PrimitiveFootprint.dereference tree d) ⟨0,by simp [Dereference.inputs]⟩ rfl (.local (.read tree d))
      token none.outputClosed leftClosed rightClosed Q P U step
  | assign tree G stable =>
    obtain ⟨m,tree,g,token,avoid⟩ := NullaryOverlap.assignment_occurrence C cert none leftClosed tree G stable f attached
    exact RetainedFootprint.primitive_allContexts_robust_case C g cert avoid free
      (BoxPermutation.PrimitiveFootprint.assignment tree G stable) ⟨0,by simp [Assignment.inputs]⟩ rfl (.local (.assign tree G stable))
      token none.outputClosed leftClosed rightClosed Q P U step
  | same tree d =>
    obtain ⟨m,tree,g,token,avoid⟩ := NullaryOverlap.same_occurrence C cert none leftClosed tree f attached
    exact RetainedFootprint.primitive_allContexts_robust_case C g cert avoid free
      (BoxPermutation.PrimitiveFootprint.same tree d) ⟨0,by simp [AtomEquality.Same.inputs]⟩ rfl (.local (.same tree d))
      token none.outputClosed leftClosed rightClosed Q P U step
  | different tree other d =>
    obtain ⟨m,n,tree,other,g,token,avoid⟩ := NullaryOverlap.different_occurrence C cert none leftClosed tree other f attached
    exact RetainedFootprint.primitive_allContexts_robust_case C g cert avoid free
      (BoxPermutation.PrimitiveFootprint.different tree other d) ⟨0,by simp [AtomEquality.Different.inputs]⟩ rfl (.local (.different tree other d))
      token none.outputClosed leftClosed rightClosed Q P U step
  | unaryArithmetic d n =>
    exact RetainedFootprint.primitive_allContexts_robust_case C f cert
      (NullaryOverlap.unary_avoids C cert none leftClosed f attached) free
      (BoxPermutation.PrimitiveFootprint.unary d n) 0 rfl (.local (.unaryArithmetic d n))
      attached none.outputClosed leftClosed rightClosed Q P U step
  | binaryArithmetic op d m n =>
    exact RetainedFootprint.primitive_allContexts_robust_case C f cert
      (NullaryOverlap.binary_avoids C cert none leftClosed op f attached) free
      (BoxPermutation.PrimitiveFootprint.binary op d m n) 0 rfl (.local (.binaryArithmetic op d m n))
      attached none.outputClosed leftClosed rightClosed Q P U step
  | beta body G stable => exact beta C cert none padding free leftClosed rightClosed body G stable f attached Q P U step
  | copy tree G copyable => exact copying C cert none free leftClosed rightClosed tree G copyable f attached Q P U step

/-- Every actual contextual rewrite supplies the required complete source occurrence. -/
theorem rewrite_case {H : Hypernet d [.term] []} {w}
    (actual : Rewrite (C.expand L) (Net.Expansion.host C L v) H w)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts none.outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := actual.local_occurrence
  exact local_case C cert none padding free leftClosed rightClosed localStep f attached Q P U step

/-- Reflection covers arbitrary representation-class successors, with no
chosen matching footprint or assumed residual-existence law. -/
theorem class_step (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts none.outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨u,original,_⟩ := StateClass.reflect step
  cases original with
  | lift finite =>
    cases finite with
    | search G s => exact False.elim (Search.no_rewrite s)
    | rewrite actual => exact rewrite_case C cert none padding free leftClosed rightClosed actual Q P U step
end NullaryResidual

/-- Reversal preserves arbitrary refinement-up-to relations and the original
unrestricted specimen, not just equality-up-to residuals. -/
theorem Specimens.converse_quasi_rel {T : PreTemplate} {Allowed}
    (closed : T.OutputClosed) {R S : StateClass → StateClass → Prop} {s t : StateClass}
    (pair : (Specimens.system T.converse Allowed closed.converse).Quasi R S s t) :
    (Specimens.system T Allowed closed).opposite.Quasi R S s t := by
  intro hs ht
  obtain ⟨w,mode,leftRoot,rightRoot,left,right⟩ := pair hs ht
  exact ⟨w.unconverse,mode,leftRoot,rightRoot,left,right⟩

/-- Every nullary padding-closed template is robust for all original contexts.
Matching steps and admissible residuals are conclusions, not premises. -/
theorem PreTemplate.NoInputs.robust {T : PreTemplate} (none : T.NoInputs)
    (padding : T.PaddingClosed) (Q P U : CostOrder) :
    (Specimens.system T Specimens.allContexts none.outputClosed).Robust Q P U := by
  intro S _ _ mode _ successor next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  change StateClass.machine.step (StateClass.ofState S.leftState) successor at next
  rw [leftEq] at next
  have result := NullaryResidual.class_step S.context S.edges none padding S.free S.left_closed S.right_closed Q P U next
  apply Or.inr
  change ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor a ∧
    StateClass.machine.Steps l (StateClass.ofState S.rightState) b ∧
    (Specimens.system T Specimens.allContexts none.outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) a b
  rw [rightEq]
  exact result
/-- Full converse robustness follows by reversing the actual nullary filling
certificates and constructing ordinary forward rewrites on the opposite side. -/
theorem PreTemplate.NoInputs.robust_converse {T : PreTemplate} (none : T.NoInputs)
    (padding : T.PaddingClosed) (Q P U : CostOrder) :
    (Specimens.system T Specimens.allContexts none.outputClosed).opposite.Robust Q P U := by
  intro S _ _ mode _ successor next
  change S.token.1 = .rewrite at mode
  have leftEq : StateClass.ofState S.leftState = StateClass.ofState
      ⟨S.depth,S.context.expand S.left,(.rewrite,Net.Expansion.host S.context S.left S.token.2)⟩ := by
    unfold Specimen.leftState Search.Expansion.position
    rw [mode]
  have rightEq : StateClass.ofState S.rightState = StateClass.ofState
      ⟨S.depth,S.context.expand S.right,(.rewrite,Net.Expansion.host S.context S.right S.token.2)⟩ := by
    unfold Specimen.rightState Search.Expansion.position
    rw [mode]
  change StateClass.machine.step (StateClass.ofState S.rightState) successor at next
  rw [rightEq] at next
  have reversePadding : T.converse.PaddingClosed := fun pair => padding pair
  obtain ⟨k,l,a,b,cost,leftSteps,rightSteps,residual⟩ :=
    NullaryResidual.class_step S.context (fun e => (S.edges e).converse)
      none.converse reversePadding S.free S.right_closed S.left_closed Q P U next
  apply Or.inr
  change ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor a ∧
    StateClass.machine.Steps l (StateClass.ofState S.leftState) b ∧
    (Specimens.system T Specimens.allContexts none.outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U) a b
  rw [leftEq]
  exact ⟨k,l,a,b,cost,leftSteps,rightSteps,Specimens.converse_quasi_rel none.outputClosed residual⟩
end Hypernets.Copying
