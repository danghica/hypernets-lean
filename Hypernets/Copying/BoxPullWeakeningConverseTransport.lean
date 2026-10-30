import Hypernets.Copying.BoxPullWeakeningReverseBeta
import Hypernets.Copying.BoxPullWeakeningReverseCopy
import Hypernets.Copying.BoxPullWeakeningReverseStore
import Hypernets.Copying.BoxPullWeakeningForwardTransport

/-! Exhaustive converse enabledness for original BPullW specimens. Every
original rule, including copying and both equality outcomes, is reconstructed
at the actual common-context token. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Opening Combined
namespace Decoration
variable {d I O} {G : Hypernet d I O} (D : Decoration G)

/-- Exhaustive dispatch over all nine original local constructors. -/
theorem local_enabled {J K} {A B : Hypernet d J K} {v w}
    (step : Local A v B w) (f : Occurrence A D.graph) :
    ∃ H : Hypernet d I O, ∃ x, Rewrite G (D.project (f.ports v)) H x := by
  cases step with
  | allocate A stable =>
    exact D.primitive_enabled f.matchEmbedding
      (ReverseComponents.allocation_nonweak A stable) (.allocate A stable)
  | read T d => exact D.read_enabled T f
  | assign T A stable => exact D.assignment_enabled T A stable f
  | same T d => exact D.same_enabled T f
  | different T U d => exact D.different_enabled T U f
  | unaryArithmetic d n =>
    exact D.primitive_enabled f.matchEmbedding
      (ReverseComponents.unary_nonweak d n) (.unaryArithmetic d n)
  | binaryArithmetic o d m n =>
    exact D.primitive_enabled f.matchEmbedding
      (ReverseComponents.binary_nonweak o d m n) (.binaryArithmetic o d m n)
  | beta B A stable => exact D.beta_enabled B A stable f
  | copy T A copyable => exact D.copying_enabled T A copyable f

/-- An arbitrary actual right rewrite supplies its own complete occurrence;
no matching or complement assumption is needed by converse enabledness. -/
theorem rewrite_enabled {H : Hypernet d I O} {v w} (step : Rewrite D.graph v H w) :
    ∃ K : Hypernet d I O, ∃ x, Rewrite G (D.project v) K x := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := step.local_occurrence
  obtain ⟨H,x,actual⟩ := D.local_enabled localStep f
  rw [attached] at actual
  exact ⟨H,x,actual⟩
end Decoration

/-- Original common-context fillings have a genuine converse matching rewrite,
including arbitrary shallow, deep and mixed template contributions. -/
theorem filling_enabled_converse {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    {v : C.Vertex} {H : Hypernet d I O} {w}
    (step : Rewrite (C.expand R) (Net.Expansion.host C R v) H w) :
    ∃ K : Hypernet d I O, ∃ x, Rewrite (C.expand L) (Net.Expansion.host C L v) K x := by
  let D := SourceNormalisation.decoration C cert free
  let rightIso := SourceNormalisation.rightIso C cert free
  let leftIso := SourceNormalisation.leftIso C cert
  have normalized := step.rename rightIso.symm (DeepIso.refl H)
  have token : Port.map rightIso.symm.vertices.toFun (Net.Expansion.host C R v) =
      Net.Expansion.host (SourceNormalisation.source C cert) D.fill v := by
    rw [← SourceNormalisation.right_token C cert free v]
    change Port.map rightIso.vertices.invFun (Port.map rightIso.vertices.toFun _) = _
    cases v with
    | input i => rfl
    | output i => rfl
    | internal i => exact congrArg Port.internal (rightIso.vertices.left_inv _)
  rw [token] at normalized
  obtain ⟨K,x,actual⟩ := D.rewrite_enabled normalized
  rw [D.project_host] at actual
  have result := actual.rename leftIso.symm (DeepIso.refl K)
  have leftToken : Port.map leftIso.symm.vertices.toFun v = Net.Expansion.host C L v := by
    have eq := SourceNormalisation.left_token C cert v
    apply Port.map_injective (fun _ _ eq => leftIso.vertices.injective eq)
    change Port.map leftIso.vertices.toFun (Port.map leftIso.vertices.invFun v) = _
    rw [eq]
    cases v with
    | input i => rfl
    | output i => rfl
    | internal i => exact congrArg Port.internal (leftIso.vertices.right_inv _)
  rw [leftToken] at result
  exact ⟨K,_,result⟩
end Hypernets.Copying.BoxPullWeakening
