import Hypernets.Copying.LambdaEntryBetaOverlap
import Hypernets.Copying.RetainedBetaMatching
import Hypernets.Copying.ConverseDeepExtraction

/-! Complete retained/deep beta branches for original lambda-entry specimens.
Only the selected function's membership in a shallow family is classified;
all argument families and every deep body contribution are preserved. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined
variable {T : PreTemplate} {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    (padding : T.PaddingClosed) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex}
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))
include cert free padding closed leftClosed rightClosed leftRoot rightRoot

/-- A retained selected function gives an actual original beta on each side
and a genuine residual, even when the argument belongs to a shallow family. -/
theorem beta_matching (heads : T.LambdaEntries) {k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : Application.Match (C.expand L) (Net.Expansion.host C L v) B)
    (function : ∀ q, C.edgeLabel a.lam.1 ≠ primitiveLabel (d+1) (.hole q)) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t :=
  Application.RetainedFrame.matching C cert free padding closed leftClosed rightClosed B
    (Application.RetainedFrame.occurrence B a)
    (beta_frame_avoids C cert heads leftClosed a function) rfl leftRoot rightRoot

/-- Every actual beta match is either the genuine shallow-function case or
a completely constructed paired original transition with an exact residual. -/
theorem beta_matching_or_shallow (heads : T.LambdaEntries) {k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : Application.Match (C.expand L) (Net.Expansion.host C L v) B) :
    (∃ q, C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.hole q)) ∨
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  classical
  by_cases shallow : ∃ q, C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.hole q)
  · exact .inl shallow
  · exact .inr (beta_matching C cert free padding closed leftClosed rightClosed leftRoot rightRoot
      heads a (by intro q eq; exact shallow ⟨q,eq⟩))

/-- The retained/deep branch has the exact quantitative robustness clause
for any independently supplied original left successor. -/
theorem beta_robust_case (heads : T.LambdaEntries) {k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : Application.Match (C.expand L) (Net.Expansion.host C L v) B)
    (function : ∀ q, C.edgeLabel a.lam.1 ≠ primitiveLabel (d+1) (.hole q))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,pair⟩ := beta_matching C cert free padding closed leftClosed rightClosed
    leftRoot rightRoot heads a function
  exact FillingWitness.matching_robust_case Q P U left right pair step

/-- An actual retained-function match on the right gives the converse
original-system clause. No left match or isolated argument witness is assumed. -/
theorem beta_converse_robust_case (heads : T.converse.LambdaEntries) {k h}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : Application.Match (C.expand R) (Net.Expansion.host C R v) B)
    (function : ∀ q, C.edgeLabel a.lam.1 ≠ primitiveLabel (d+1) (.hole q))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,right,left,pair⟩ := beta_matching C (fun e => (cert e).converse) free padding.converse
    closed.converse rightClosed leftClosed rightRoot leftRoot heads a function
  exact FillingWitness.matching_robust_case Q P U right left (Specimens.converse_quasi closed pair) step
end Hypernets.Copying.LambdaEntryOverlap
