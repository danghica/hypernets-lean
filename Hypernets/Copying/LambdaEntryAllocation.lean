import Hypernets.Copying.RetainedReplacement
import Hypernets.Copying.ParametricityBoundaryBarrier
import Hypernets.Copying.FramedFillingTransfer

/-! Complete allocation overlap for lambda-entry templates. A stable lambda
may belong to a multi-input shallow filling: only the retained ref edge is
rewritten, while that whole original filling remains in the residual. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined Search.Expansion

/-- A non-hole primitive in the original context has literal corolla copies
on both sides of an original recursive filling certificate. -/
theorem DeepFillingEdge.primitive_copies {T d I O} {C : Hypernet d I O} {L R e p}
    (cert : DeepFillingEdge T C L R e) (label : C.edgeLabel e = primitiveLabel d p)
    (notHole : ∀ h, p ≠ .hole h) :
    Nonempty (LabelCopy (L e) (C.edgeLabel e) × LabelCopy (R e) (C.edgeLabel e)) := by
  cases cert with
  | retained l r => exact ⟨l,r⟩
  | filled h hole rel => exact False.elim (notHole h (primitiveLabel_injective d (label.symm.trans hole)))
  | boxed b boxLabel inner l r => rw [boxLabel] at label; cases label

namespace LambdaEntryOverlap
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (outputClosed : T.OutputClosed)
include cert free leftClosed rightClosed outputClosed

/-- An unchanged original ref head gives the complete one-step/one-step
matching diagram. Stability on each side is proved from its actual rooted
search history; the original multi-edge arguments need not be retained. -/
theorem retained_allocation_matching {v : C.Vertex} {e : C.Edge}
    (head : MatchEmbedding.HeadAt C v e (.operation (.unary .ref)))
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v)) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  obtain ⟨l,r⟩ := (cert e).primitive_copies head.1 (by intro h eq; cases eq)
  have left := Allocation.Retained.rooted_rewrite C e head.1 l head leftRoot
  have right := Allocation.Retained.rooted_rewrite C e head.1 r head rightRoot
  let w := Allocation.Retained.pointed C cert free e head.1 v
  have typed : C.vertexLabel v = .term := by
    have mem := List.mem_map_of_mem (f := C.vertexLabel) head.2
    dsimp only [Net.vertexLabel] at mem
    rw [C.source_typed,head.1,primitive_input] at mem
    exact List.mem_singleton.mp mem
  refine ⟨_,_,StateClass.project (.lift (.rewrite left)),StateClass.project (.lift (.rewrite right)),?_⟩
  exact w.quasi outputClosed (rewrite_holeFree left leftClosed) (rewrite_holeFree right rightClosed)
    ((Net.Expansion.host_label _ _ _).trans typed)

omit free leftClosed rightClosed outputClosed in
/-- The actual ref edge at an original host token is retained, although its
stable lambda operand may lie inside any shallow lambda-entry family. -/
theorem allocation_head (heads : T.LambdaEntries) {v : C.Vertex} {e : (C.expand L).Edge}
    (head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) e
      (.operation (.unary .ref))) :
    MatchEmbedding.HeadAt C v e.1 (.operation (.unary .ref)) := by
  obtain ⟨copy⟩ := source_retained C cert heads head.2 (by
    rw [head.1]
    intro eq
    cases primitiveLabel_injective d eq)
  refine ⟨(copy.primitive _).mp ?_,source_owner C L head.2⟩
  change (L e.1).edgeLabel copy.edge = _
  exact (copy.only e.2) ▸ head.1

/-- Every actual allocation overlap has an opposite original step and a
genuine original residual, including shallow lambda operands and deep boxes. -/
theorem allocation_matching (heads : T.LambdaEntries) {K}
    (G : Hypernet d [.term] K) (_stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v)) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi Eq Eq s t := by
  have head := f.matchEmbedding.head (Allocation.head_at G)
  change MatchEmbedding.HeadAt (C.expand L) (f.ports (.input 0))
    (f.edges (Allocation.head G)) (.operation (.unary .ref)) at head
  rw [attached] at head
  exact retained_allocation_matching C cert free leftClosed rightClosed outputClosed
    (allocation_head C cert heads head) leftRoot rightRoot

/-- The exact robust case quantifies over every independently supplied
successor of the original machine. -/
theorem allocation_robust_case (heads : T.LambdaEntries) {K}
    (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R v))
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,residual⟩ := allocation_matching C cert free leftClosed rightClosed outputClosed
    heads G stable f attached leftRoot rightRoot
  exact FillingWitness.matching_robust_case Q P U left right residual step

end LambdaEntryOverlap
end Hypernets.Copying
