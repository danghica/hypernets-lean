import Hypernets.Copying.BoxPullContractionReverseBarrier
import Hypernets.Copying.RetainedRewriteTransfer
import Hypernets.Copying.ArithmeticLocalReduction
import Hypernets.Copying.OperationalPrimitiveOverlap

/-! Allocation and arithmetic footprints cannot enter BPullC right-hand holes.
The proof follows their actual head-to-operand paths and requires neither
binding freedom nor a rooted execution history. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReversePrimitive
open Graph
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R))
include cert closed

/-- A complete local footprint whose edges are descendants of its sourced
head avoids every original shallow BPullC hole. -/
theorem sourced_ancestors_avoid {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A (C.expand R)) {a : A.Vertex} {head : A.Edge}
    (primitive : BoxPermutation.PrimitiveFootprint A)
    (source : a ∈ A.source head) (paths : ∀ e, Ancestor A head e)
    {v : C.Vertex} (attached : f.ports a = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  have selected : Net.Expansion.host C R v ∈ (C.expand R).source (f.edges head) := by
    rw [← attached]
    exact f.matchEmbedding.source_mem source
  intro e
  exact right_primitive_ancestry C cert closed f.matchEmbedding primitive selected (paths e)

/-- Allocation inspects its ref head and the original stable operand, all of
which are connected directly to that head in the actual source graph. -/
theorem allocation_avoids {U} (G : Hypernet d [.term] U) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  apply sourced_ancestors_avoid C cert closed f (BoxPermutation.PrimitiveFootprint.allocation G stable) (Allocation.head_at G).2 _ attached
  intro ⟨part,e⟩
  cases part with
  | false =>
    cases d
    all_goals
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      exact .refl _
  | true =>
    cases d
    all_goals
      apply Ancestor.step _ (.refl _)
      refine ⟨.internal (.inl (0 : Fin 1)),List.mem_cons_self,?_⟩
      exact List.mem_map_of_mem (Stable.input_source stable.labels e)

/-- Unary negation inspects exactly the selected operation and numeric operand. -/
theorem unary_avoids {n} (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand R))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  apply sourced_ancestors_avoid C cert closed f (BoxPermutation.PrimitiveFootprint.unary d n) (Arithmetic.unary_head d n).2 _ attached
  intro e
  classical
  by_cases eq : e = Arithmetic.unaryHead d n
  · subst e; exact .refl _
  · exact .step ((Arithmetic.unary_adjacent_iff d n e).mpr eq) (.refl _)

/-- Binary arithmetic inspects the selected operation and both ordered
numeric operands; either original binary arithmetic code is permitted. -/
theorem binary_avoids (o : Arithmetic.BinaryCode) {m n}
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand R))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  apply sourced_ancestors_avoid C cert closed f (BoxPermutation.PrimitiveFootprint.binary o d m n) (Arithmetic.binary_head o d m n).2 _ attached
  intro e
  classical
  by_cases eq : e = Arithmetic.binaryHead o d m n
  · subst e; exact .refl _
  · exact .step ((Arithmetic.binary_adjacent_iff o d m n e).mpr eq) (.refl _)

theorem allocation_enabled {U} (G : Hypernet d [.term] U) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand R)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) f.matchEmbedding
    (allocation_avoids C cert closed G stable f attached)
    (BoxPermutation.PrimitiveFootprint.allocation G stable) (.allocate G stable) attached

theorem unary_enabled {n} (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand R))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) f.matchEmbedding
    (unary_avoids C cert closed f attached)
    (BoxPermutation.PrimitiveFootprint.unary d n) (.unaryArithmetic d n) attached

theorem binary_enabled (o : Arithmetic.BinaryCode) {m n}
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand R))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  exact RetainedFootprint.primitive_local C (fun e => (cert e).converse) f.matchEmbedding
    (binary_avoids C cert closed o f attached)
    (BoxPermutation.PrimitiveFootprint.binary o d m n) (.binaryArithmetic o d m n) attached

end Hypernets.Copying.BoxPullContraction.ReversePrimitive
