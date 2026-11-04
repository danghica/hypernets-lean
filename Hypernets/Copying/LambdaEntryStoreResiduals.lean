import Hypernets.Copying.LambdaEntryStoreOverlap
import Hypernets.Copying.NullaryPrimitiveResiduals
import Hypernets.Copying.ConverseSpecimenTransfer

/-! Actual one-step read and atom-equality residuals for every original
lambda-entry, closed-output filling, in both directions. All matched trees,
store identities and contents outputs remain unchanged; shallow footprint
retention is proved rather than assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoOutputs)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (outputClosed : T.OutputClosed)
include cert none free leftClosed rightClosed outputClosed

/-- The actual dereference has a matched original step on the other
filling and a genuine residual specimen in the unrestricted context class. -/
theorem read_matching (heads : T.LambdaEntries) {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C L v) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  obtain ⟨left,right,residual⟩ := RetainedFootprint.primitive_allContexts_input_diamond C f cert
    (read_avoids C cert heads none leftClosed tree f attached) free
    (BoxPermutation.PrimitiveFootprint.dereference tree d) ⟨0,by simp [Dereference.inputs]⟩ rfl (.local (.read tree d))
    attached outputClosed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),residual⟩

/-- Every independently supplied dereference successor satisfies
the original quantitative robustness clause, with one transition per side. -/
theorem read_robust_case (heads : T.LambdaEntries) {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,residual⟩ := read_matching C cert none free leftClosed rightClosed outputClosed
    heads tree f attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

/-- An actual right dereference occurrence yields the converse clause
in the opposite of the original specimen system, with no symmetry premise. -/
theorem read_converse_robust_case (heads : T.converse.LambdaEntries) {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,right,left,residual⟩ := read_matching C (fun e => (cert e).converse) none.converse
    free rightClosed leftClosed outputClosed.converse heads tree f attached
  exact FillingWitness.matching_robust_case Q P U right left (Specimens.converse_quasi outputClosed residual) step

/-- The actual same-store atom equality has a matched original step on the other
filling and a genuine residual specimen in the unrestricted context class. -/
theorem same_matching (heads : T.LambdaEntries) {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C L v) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  obtain ⟨left,right,residual⟩ := RetainedFootprint.primitive_allContexts_input_diamond C f cert
    (same_avoids C cert heads none leftClosed tree f attached) free
    (BoxPermutation.PrimitiveFootprint.same tree d) ⟨0,by simp [AtomEquality.Same.inputs]⟩ rfl (.local (.same tree d))
    attached outputClosed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),residual⟩

/-- Every independently supplied same-store atom equality successor satisfies
the original quantitative robustness clause, with one transition per side. -/
theorem same_robust_case (heads : T.LambdaEntries) {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,residual⟩ := same_matching C cert none free leftClosed rightClosed outputClosed
    heads tree f attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

/-- An actual right same-store atom equality occurrence yields the converse clause
in the opposite of the original specimen system, with no symmetry premise. -/
theorem same_converse_robust_case (heads : T.converse.LambdaEntries) {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,right,left,residual⟩ := same_matching C (fun e => (cert e).converse) none.converse
    free rightClosed leftClosed outputClosed.converse heads tree f attached
  exact FillingWitness.matching_robust_case Q P U right left (Specimens.converse_quasi outputClosed residual) step

/-- The actual distinct-store atom equality has a matched original step on the other
filling and a genuine residual specimen in the unrestricted context class. -/
theorem different_matching (heads : T.LambdaEntries) {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (AtomEquality.Different.before tree other d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L v) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  obtain ⟨left,right,residual⟩ := RetainedFootprint.primitive_allContexts_input_diamond C f cert
    (different_avoids C cert heads none leftClosed tree other f attached) free
    (BoxPermutation.PrimitiveFootprint.different tree other d) ⟨0,by simp [AtomEquality.Different.inputs]⟩ rfl (.local (.different tree other d))
    attached outputClosed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),residual⟩

/-- Every independently supplied distinct-store atom equality successor satisfies
the original quantitative robustness clause, with one transition per side. -/
theorem different_robust_case (heads : T.LambdaEntries) {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (AtomEquality.Different.before tree other d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,residual⟩ := different_matching C cert none free leftClosed rightClosed outputClosed
    heads tree other f attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

/-- An actual right distinct-store atom equality occurrence yields the converse clause
in the opposite of the original specimen system, with no symmetry premise. -/
theorem different_converse_robust_case (heads : T.converse.LambdaEntries) {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (AtomEquality.Different.before tree other d) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,right,left,residual⟩ := different_matching C (fun e => (cert e).converse) none.converse
    free rightClosed leftClosed outputClosed.converse heads tree other f attached
  exact FillingWitness.matching_robust_case Q P U right left (Specimens.converse_quasi outputClosed residual) step

end Hypernets.Copying.LambdaEntryOverlap
