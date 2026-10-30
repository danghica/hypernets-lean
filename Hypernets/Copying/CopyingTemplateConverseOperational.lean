import Hypernets.Copying.CopyingTemplateConversePrimitive
import Hypernets.Copying.CopyingTemplateConverseBeta
import Hypernets.Copying.CopyingTemplateConverseStoreFootprint
import Hypernets.Copying.CopyingTemplateRetainedConverse

/-! Every original operational converse case for the copying template. The
actual left rooted search history excludes already evaluated shallow holes;
selected atom subtrees retain every operation/store attachment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ConverseResidual
open Graph Combined Search.Expansion

/-- The eight operation-headed rules all produce genuine opposite steps and
unrestricted original residual specimens. Allocation, arithmetic and beta use
the supplied source; store rules prune only irrelevant contraction siblings. -/
theorem operational_case {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (free : FocusFree C) (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L v))
    {J K} {A B : Hypernet d J K} {a b}
    (localStep : Local A a B b) (f : Opening.Occurrence A (C.expand R))
    (operational : ∃ e o, MatchEmbedding.HeadAt A a e (.operation o))
    (attached : f.ports a = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  cases localStep with
  | allocate G stable =>
    have avoid := ConverseOverlap.allocation_avoids C cert leftClosed away rooted G stable f attached
    exact retained_local_case C cert free leftClosed rightClosed (.allocate G stable) f avoid attached Q P U step
  | read tree d =>
    obtain ⟨n,tree,g,token,avoid⟩ :=
      ConverseStoreFootprint.read_occurrence C cert leftClosed rightClosed away rooted tree f attached
    exact retained_local_case C cert free leftClosed rightClosed (.read tree d) g avoid token Q P U step
  | assign tree G stable =>
    obtain ⟨n,tree,g,token,avoid⟩ :=
      ConverseStoreFootprint.assignment_occurrence C cert leftClosed rightClosed away rooted tree G stable f attached
    exact retained_local_case C cert free leftClosed rightClosed (.assign tree G stable) g avoid token Q P U step
  | same tree d =>
    obtain ⟨n,tree,g,token,avoid⟩ :=
      ConverseStoreFootprint.same_occurrence C cert leftClosed rightClosed away rooted tree f attached
    exact retained_local_case C cert free leftClosed rightClosed (.same tree d) g avoid token Q P U step
  | different tree other d =>
    obtain ⟨n,m,tree,other,g,token,avoid⟩ :=
      ConverseStoreFootprint.different_occurrence C cert leftClosed rightClosed away rooted tree other f attached
    exact retained_local_case C cert free leftClosed rightClosed (.different tree other d) g avoid token Q P U step
  | unaryArithmetic d n =>
    have avoid := ConverseOverlap.unary_avoids C cert leftClosed away rooted n f attached
    exact retained_local_case C cert free leftClosed rightClosed (.unaryArithmetic d n) f avoid attached Q P U step
  | binaryArithmetic op d m n =>
    have avoid := ConverseOverlap.binary_avoids C cert leftClosed away rooted op m n f attached
    exact retained_local_case C cert free leftClosed rightClosed (.binaryArithmetic op d m n) f avoid attached Q P U step
  | beta body G stable =>
    have avoid := ConverseOverlap.beta_avoids C cert leftClosed away rooted body G stable f attached
    exact retained_local_case C cert free leftClosed rightClosed (.beta body G stable) f avoid attached Q P U step
  | copy tree G copyable =>
    obtain ⟨e,o,head⟩ := operational
    obtain ⟨e',contr⟩ := CopyRule.before_active_head tree G ⟨0,by simp⟩
    exact False.elim (by have bad := (MatchEmbedding.head_unique head contr).2; cases bad)

end Hypernets.Copying.CopyingTemplate.ConverseResidual
