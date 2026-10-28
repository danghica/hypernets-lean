import Hypernets.Copying.ConverseStoreFootprint
import Hypernets.Copying.ConverseSpecimenTransfer
import Hypernets.Copying.AllocationAssignmentResiduals
import Hypernets.Copying.PrimitiveGuardedTransfer

/-! Universal converse read and assignment residuals. The complete footprint
is constructed from the supplied right rule by pruning unused atom siblings;
no left match or shallow-overlap/admissibility premise is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)

include cert free away rooted

/-- Extract the actual selected atom spine of any original right read, with
all original operation/store attachments and a proved retained footprint. -/
theorem read_occurrence {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand R))
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C R v) :
    ∃ m, ∃ spine : ContractionTree .atom (m+1),
      ∃ g : Opening.Occurrence (Dereference.before spine d) (C.expand R),
        g.ports (Dereference.inputPort m 0) = Net.Expansion.host C R v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := tree.minimal_spine d ⟨0,by simp⟩
  let spine := ContractionSpine.tree .atom n orientation
  let treeMap : Opening.Occurrence (spine.atDepth d) (tree.atDepth d) := g
  let matched := (Dereference.TreeRematch.occurrence treeMap first last).comp f
  refine ⟨n+1,spine,matched,?_,?_⟩
  · exact attached
  · exact ConverseOverlap.read_subtree_avoids C cert free away rooted spine tree treeMap first last
      (fun e => ⟨a,e.val,entry,paths e⟩) f attached

/-- Selected-spine extraction retains the literal stable assignment value,
its output ordering, the selected store and both value connections. -/
theorem assignment_occurrence {h O} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand R))
    (attached : f.ports (Assignment.inputPort h O 0) = Net.Expansion.host C R v) :
    ∃ m, ∃ spine : ContractionTree .atom (m+1),
      ∃ g : Opening.Occurrence (Assignment.before spine G) (C.expand R),
        g.ports (Assignment.inputPort m O 0) = Net.Expansion.host C R v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := tree.minimal_spine d ⟨0,by simp⟩
  let spine := ContractionSpine.tree .atom n orientation
  let treeMap : Opening.Occurrence (spine.atDepth d) (tree.atDepth d) := g
  let matched := (Assignment.TreeRematch.occurrence treeMap G first last).comp f
  refine ⟨n+1,spine,matched,?_,?_⟩
  · change f.ports ((Assignment.TreeRematch.occurrence treeMap G first last).ports _) = _
    rw [Assignment.TreeRematch.occurrence_input]
    exact attached
  · exact ConverseOverlap.assignment_subtree_avoids C cert free away rooted spine tree treeMap first last
      (fun e => ⟨a,e.val,entry,paths e⟩) G stable f attached

include leftClosed rightClosed

/-- Every actual right read has a corresponding actual left read and an
admissible residual in the opposite original operational specimen system. -/
theorem read_diamond {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand R))
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C R v) :
    ∃ H K : Hypernet d [.term] [], ∃ a b,
      Rewrite (C.expand R) (Net.Expansion.host C R v) H a ∧
      Rewrite (C.expand L) (Net.Expansion.host C L v) K b ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi Eq Eq
        (StateClass.ofState ⟨d,H,(.search,a)⟩) (StateClass.ofState ⟨d,K,(.search,b)⟩) := by
  obtain ⟨m,spine,g,token,avoid⟩ := read_occurrence C cert free away rooted tree f attached
  obtain ⟨right,left,residual⟩ := primitive_guarded_diamond C g (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.dereference spine d) (Dereference.before_bindingGuarded spine d)
    (Dereference.focusFree_sides spine d).2 (Dereference.holeFree_sides spine d).2 token rfl
    (.local (.read spine d)) (PreTemplate.OutputClosed.converse (template_outputClosed kind)) rightClosed leftClosed
  exact ⟨_,_,_,_,right,left,Specimens.converse_quasi (template_outputClosed kind) residual⟩

/-- Every actual right assignment has a corresponding actual left assignment
for all original stable operands, including their possible thunk outputs. -/
theorem assignment_diamond {h O} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand R))
    (attached : f.ports (Assignment.inputPort h O 0) = Net.Expansion.host C R v) :
    ∃ H K : Hypernet d [.term] [], ∃ a b,
      Rewrite (C.expand R) (Net.Expansion.host C R v) H a ∧
      Rewrite (C.expand L) (Net.Expansion.host C L v) K b ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi Eq Eq
        (StateClass.ofState ⟨d,H,(.search,a)⟩) (StateClass.ofState ⟨d,K,(.search,b)⟩) := by
  obtain ⟨m,spine,g,token,avoid⟩ := assignment_occurrence C cert free away rooted tree G stable f attached
  obtain ⟨right,left,residual⟩ := primitive_thunk_diamond C g (fun e => (cert e).converse) avoid free
    (BoxPermutation.PrimitiveFootprint.assignment spine G stable) (Assignment.before_bindingOrThunk spine G stable)
    (holeTermInputs C cert leftClosed) (Assignment.stable_assignment_safe spine G stable).2.2.1
    (Assignment.stable_assignment_safe spine G stable).2.2.2 token rfl (.local (.assign spine G stable))
    (PreTemplate.OutputClosed.converse (template_outputClosed kind)) rightClosed leftClosed
  exact ⟨_,_,_,_,right,left,Specimens.converse_quasi (template_outputClosed kind) residual⟩

/-- Quantitative converse reading for any supplied actual right successor. -/
theorem read {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand R))
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,K,a,b,right,left,residual⟩ := read_diamond C cert free away leftClosed rightClosed rooted tree f attached
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left))) residual step

/-- Quantitative converse assignment for any supplied actual right successor. -/
theorem assignment {h O} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand R))
    (attached : f.ports (Assignment.inputPort h O 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨H,K,a,b,right,left,residual⟩ := assignment_diamond C cert free away leftClosed rightClosed rooted tree G stable f attached
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite right))) (StateClass.project (.lift (.rewrite left))) residual step

end Hypernets.Copying.OperationalTemplates.ConverseResidual
