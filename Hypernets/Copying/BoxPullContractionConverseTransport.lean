import Hypernets.Copying.BoxPullContractionReverseBeta
import Hypernets.Copying.BoxPullContractionReverseCopy
import Hypernets.Copying.BoxPullContractionReverseStore
import Hypernets.Copying.BoxPullContractionForwardTransport

/-! Exhaustive actual converse matching for the original BPullC specimen.
All nine original local rules are reconstructed at the original host token;
unused contraction siblings and new right internal vertices are never assumed
retained or projected globally. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Opening Combined
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) (free : FocusFree C)
include cert closed free

/-- Exhaustive reconstruction of an actual left rewrite from any original
right local rule occurrence and its actual original context coordinate. -/
theorem local_enabled_converse {J K} {A B : Hypernet d J K} {a b}
    (step : Local A a B b) (f : Occurrence A (C.expand R)) {v : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  cases step with
  | allocate G stable => exact ReversePrimitive.allocation_enabled C cert closed G stable f attached
  | read T d => exact ReverseStore.read_enabled C cert closed T f attached
  | assign T G stable => exact ReverseStore.assignment_enabled C cert closed T G stable f attached
  | same T d => exact ReverseStore.same_enabled C cert closed T f attached
  | different T U d => exact ReverseStore.different_enabled C cert closed T U f attached
  | unaryArithmetic d n => exact ReversePrimitive.unary_enabled C cert closed f attached
  | binaryArithmetic o d m n => exact ReversePrimitive.binary_enabled C cert closed o f attached
  | beta B G stable => exact ReverseBeta.beta_enabled C cert free closed B G stable f attached
  | copy T G copyable => exact ReverseCopy.copying_enabled C cert closed free T G copyable f attached

/-- Every supplied right whole-graph rewrite contains its own complete local
occurrence. Its reconstructed left rewrite uses the exact paired specimen token. -/
theorem filling_enabled_converse {v : C.Vertex} {H : Hypernet d I O} {w}
    (step : Rewrite (C.expand R) (Net.Expansion.host C R v) H w) :
    ∃ K : Hypernet d I O, ∃ x, Rewrite (C.expand L) (Net.Expansion.host C L v) K x := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := step.local_occurrence
  exact local_enabled_converse C cert closed free localStep f attached

end Hypernets.Copying.BoxPullContraction
