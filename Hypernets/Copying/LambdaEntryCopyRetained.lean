import Hypernets.Copying.LambdaEntryCopyTrace
import Hypernets.Copying.LambdaEntryStoreOverlap
import Hypernets.Copying.UnrestrictedDeepLocal
import Hypernets.Copying.NullaryRobustness

/-! The retained-payload copy branch preserves the complete original tree,
including all unused siblings. Deep template holes in the actual lambda box
are transported by the proved unrestricted copying residual construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryCopy
open Graph Opening Search.Expansion Combined RetainedFootprint
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (none : T.NoOutputs) (closed : HoleFree (C.expand L))

include cert heads closed
/-- Retaining the actual payload head retains its entire outer payload.
The possible lambda box is reached through the head's original thunk output
and cannot be the lambda head at any shallow-family input. -/
theorem payload_avoids {k h} {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand L))
    (head : Nonempty (Retained C L (payload.edges normal.head).1)) :
    ∀ e name, C.edgeLabel (payload.edges e).1 ≠ primitiveLabel d (.hole name) := by
  obtain ⟨copy⟩ := head
  intro e name
  rcases normal.edge_cases e with rfl | rfl
  · exact LambdaEntryOverlap.retained_not_hole C closed copy name
  · cases normal with
    | plain d c => exact LambdaEntryOverlap.retained_not_hole C closed copy name
    | lambda B =>
      have adj : (lambdaPayload B).Adjacent (CopyRule.NormalForm.lambda B).head (CopyRule.NormalForm.lambda B).tail :=
        ⟨.internal (CopyRule.NormalForm.lambdaWire B),List.mem_cons_self,List.mem_cons_self⟩
      obtain ⟨w,target,source⟩ := payload.matchEmbedding.adjacent adj
      obtain ⟨v,eq⟩ := copy.target_origin target
      apply LambdaEntryOverlap.source_not_hole C cert heads closed (eq ▸ source) _ name
      intro label
      have original := (Search.primitive_equiv (payload.label (CopyRule.NormalForm.lambda B).tail)
        (.operation .lam)).mpr label
      cases original

include cert heads none closed
/-- Every edge of the whole original copying source avoids shallow holes
once its actual payload head is retained. The no-output law works backwards
from the payload through every branch of the supplied tree. -/
theorem source_avoids {m k h} (tree : ContractionTree .term (m+1))
    {V : Hypernet d [.term] (environmentInterface k h)} (normal : CopyRule.NormalForm V)
    (f : Occurrence (CopyRule.before tree V) (C.expand L))
    (head : Nonempty (Retained C L
      (f.edges (Serial.rightEdge (CopyRule.tree tree d) V normal.head)).1)) :
    AvoidsShallow C f.matchEmbedding := by
  have payload := payload_avoids C cert heads closed normal
    ((Occurrence.serialRight (CopyRule.tree tree d) V).comp f) head
  have trees (e : tree.net.Edge) : ∀ name,
      C.edgeLabel (f.edges (Serial.leftEdge (CopyRule.tree tree d) V e)).1 ≠ primitiveLabel d (.hole name) := by
    obtain ⟨n,path⟩ := tree.reaches_root e
    have before := CopyTrace.snoc
      (path.map (Serial.leftEdge (CopyRule.tree tree d) V) (CopyRule.before_tree_hop tree V))
      (CopyRule.before_root_hop tree V normal.head_at)
    exact LambdaEntryOverlap.ancestor_of_retained_not_hole C cert none closed f
      (CopyTrace.ancestor before) head
  cases d
  all_goals
    rintro ⟨side,e⟩
    cases side
    · exact trees e
    · exact payload e

end Hypernets.Copying.LambdaEntryCopy

namespace Hypernets.Copying.LambdaEntryCopy
open Graph Opening Search.Expansion Combined RetainedFootprint
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (none : T.NoOutputs) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (outputClosed : T.OutputClosed)
include cert heads none free leftClosed rightClosed outputClosed

/-- The retained-payload branch has actual one-step successors and a genuine
original residual in arbitrary contexts, preserving the supplied whole tree
and arbitrary deep template holes inside the copied lambda body. -/
theorem retained_matching {m k h} (tree : ContractionTree .term (m+1))
    {V : Hypernet d [.term] (environmentInterface k h)} (normal : CopyRule.NormalForm V)
    (f : Occurrence (CopyRule.before tree V) (C.expand L))
    (head : Nonempty (Retained C L
      (f.edges (Serial.rightEdge (CopyRule.tree tree d) V normal.head)).1))
    {v : C.Vertex} (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  have avoid := source_avoids C cert heads none leftClosed tree normal f head
  obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.copying_local C cert free tree V normal.copyable f avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f cert avoid free ⟨0,by simp⟩
    (List.getElem_replicate _) (.local (.copy tree V normal.copyable)) paired w attached outputClosed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),residual⟩

/-- The retained branch handles any independently supplied original copying
successor, after its actual head-retention case has been classified. -/
theorem retained_robust_case {m k h} (tree : ContractionTree .term (m+1))
    {V : Hypernet d [.term] (environmentInterface k h)} (normal : CopyRule.NormalForm V)
    (f : Occurrence (CopyRule.before tree V) (C.expand L))
    (head : Nonempty (Retained C L
      (f.edges (Serial.rightEdge (CopyRule.tree tree d) V normal.head)).1))
    {v : C.Vertex} (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,residual⟩ := retained_matching C cert heads none free leftClosed rightClosed outputClosed
    tree normal f head attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

omit heads in
/-- Reversing the actual original certificates proves the retained copying
branch in the opposite specimen system without a symmetry hypothesis. -/
theorem retained_converse_robust_case (reverseHeads : T.converse.LambdaEntries)
    {m k h} (tree : ContractionTree .term (m+1))
    {V : Hypernet d [.term] (environmentInterface k h)} (normal : CopyRule.NormalForm V)
    (f : Occurrence (CopyRule.before tree V) (C.expand R))
    (head : Nonempty (Retained C R
      (f.edges (Serial.rightEdge (CopyRule.tree tree d) V normal.head)).1))
    {v : C.Vertex} (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,right,left,residual⟩ := retained_matching C (fun e => (cert e).converse)
    reverseHeads none.converse free rightClosed leftClosed outputClosed.converse tree normal f head attached
  exact FillingWitness.matching_robust_case Q P U right left (Specimens.converse_quasi outputClosed residual) step

end Hypernets.Copying.LambdaEntryCopy
