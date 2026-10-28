import Hypernets.Copying.OperationalPrimitiveOverlap
import Hypernets.Copying.OperationalBetaOverlap
import Hypernets.Copying.OperationalCopyOverlap
import Hypernets.Copying.RewriteCutFactorization

/-! Complete forward overlap classification for both original operational
templates. Every original contextual compute derivation admits its actual
full-label local occurrence, and all its outer edges avoid shallow template
holes. Deep occurrences inside original boxes remain permitted. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ForwardOverlap
open Graph Search.Expansion Opening
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
include cert free away

/-- Exhaustive no-shallow-overlap proof for all nine original local rule
constructors. In particular, arbitrary original sharing trees and the full
stable-value premises are preserved. -/
theorem local_avoids {J K} {A B : Hypernet d J K} {a b}
    (step : Combined.Local A a B b) (f : Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  cases step with
  | allocate G stable =>
    exact primitive_avoids C cert away f.matchEmbedding (Allocation.head_at G) attached
      (allocation_cases G stable)
  | read T d =>
    exact primitive_avoids C cert away f.matchEmbedding (Dereference.localMatch T d).head attached
      (read_cases T d)
  | assign T G stable =>
    exact primitive_avoids C cert away f.matchEmbedding (Assignment.localMatch T G).head attached
      (assignment_cases T G stable)
  | same T d =>
    exact primitive_avoids C cert away f.matchEmbedding (AtomEquality.Same.head_at T d) attached
      (same_cases T d)
  | different T U d =>
    exact primitive_avoids C cert away f.matchEmbedding (AtomEquality.Different.head_at T U d) attached
      (different_cases T U d)
  | unaryArithmetic d n =>
    exact primitive_avoids C cert away f.matchEmbedding (Arithmetic.unary_head d n) attached
      (unary_cases d n)
  | binaryArithmetic o d m n =>
    exact primitive_avoids C cert away f.matchEmbedding (Arithmetic.binary_head o d m n) attached
      (binary_cases o d m n)
  | beta B G stable => exact beta_avoids C cert away B G stable f attached
  | copy tree H copyable => exact copy_avoids C cert free away tree copyable f attached

/-- Starting from an actual original whole-graph rewrite at a non-entering
binding-free specimen token, construct its original local rule and a complete
recursive-label occurrence with a proved shallow-hole-free footprint. This
covers every rename, plug and simultaneous-expansion constructor; no overlap
classification or matching certificate is assumed by the caller. -/
theorem rewrite_occurrence {H : Hypernet d I O} {w}
    (step : Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w) :
    ∃ J K, ∃ A B : Hypernet d J K, ∃ a b, Combined.Local A a B b ∧
      ∃ f : Occurrence A (C.expand L), f.ports a = Net.Expansion.host C L v ∧
        RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := step.local_occurrence
  exact ⟨J,K,A,B,a,b,localStep,f,attached,
    local_avoids C cert free away localStep f attached⟩

/-- The same complete no-shallow classification accompanies an explicit
finite cut of the actual supplied rewrite, including the recursive isomorphism
identifying its original successor graph and resumed token. -/
theorem rewrite_cut {H : Hypernet d I O} {w}
    (step : Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w) :
    Nonempty {cut : Combined.CutFactorization
      (C.expand L) (Net.Expansion.host C L v) H w //
      RetainedFootprint.AvoidsShallow C cut.occurrence.matchEmbedding} := by
  obtain ⟨cut⟩ := step.cut_factorization
  exact ⟨⟨cut,local_avoids C cert free away cut.localStep cut.occurrence cut.token⟩⟩

end Hypernets.Copying.OperationalTemplates.ForwardOverlap
