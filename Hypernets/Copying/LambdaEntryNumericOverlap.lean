import Hypernets.Copying.ParametricityBoundaryBarrier
import Hypernets.Copying.NullaryPrimitiveResiduals
import Hypernets.Copying.ArithmeticLocalReduction

/-! Arithmetic footprints cannot cross a lambda-family entry. These actual
matching diagrams apply to both directions of Figure 20 parametricity. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (closed : HoleFree (C.expand L))
include cert heads closed

/-- Every edge of a sourced non-lambda ancestry avoids shallow family
holes. The proof follows real component incidences, without rootedness. -/
theorem ancestor_not_hole {J K} {A : Hypernet d J K}
    (f : MatchEmbedding A (C.expand L))
    (different : ∀ e, (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel d (.operation .lam))
    {v : C.Vertex} {a b : A.Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges a))
    (path : Ancestor A a b) :
    ∀ h, C.edgeLabel (f.edges b).1 ≠ primitiveLabel d (.hole h) := by
  induction path generalizing v with
  | refl => exact source_not_hole C cert heads closed source (different _)
  | step adj path ih =>
    obtain ⟨copy⟩ := source_retained C cert heads source (different _)
    obtain ⟨w,target,next⟩ := f.adjacent adj
    obtain ⟨u,eq⟩ := copy.target_origin target
    exact ih (eq ▸ next)

/-- The complete actual unary arithmetic match is retained. -/
theorem unary_avoids {n} (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand L))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  have different (e) : (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel d (.operation .lam) := by
    intro label
    have original := (Search.primitive_equiv (f.label e) (.operation .lam)).mpr label
    obtain ⟨b,e⟩ := e
    cases d <;> cases b <;> cases original
  have sourced : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges (Arithmetic.unaryHead d n)) := by
    rw [← attached]
    exact f.matchEmbedding.source_mem (Arithmetic.unary_head d n).2
  intro e
  apply ancestor_not_hole C cert heads closed f.matchEmbedding different sourced
  classical
  by_cases eq : e = Arithmetic.unaryHead d n
  · subst e; exact .refl _
  · exact .step ((Arithmetic.unary_adjacent_iff d n e).mpr eq) (.refl _)

/-- Both ordered numeric operands remain in the unchanged context. -/
theorem binary_avoids (o : Arithmetic.BinaryCode) {m n}
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand L))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  have different (e) : (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel d (.operation .lam) := by
    intro label
    have original := (Search.primitive_equiv (f.label e) (.operation .lam)).mpr label
    obtain ⟨b,e⟩ := e
    cases b with
    | false => cases d <;> cases o <;> cases original
    | true => cases d <;> obtain ⟨b,e⟩ := e <;> cases b <;> cases original
  have sourced : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges (Arithmetic.binaryHead o d m n)) := by
    rw [← attached]
    exact f.matchEmbedding.source_mem (Arithmetic.binary_head o d m n).2
  intro e
  apply ancestor_not_hole C cert heads closed f.matchEmbedding different sourced
  classical
  by_cases eq : e = Arithmetic.binaryHead o d m n
  · subst e; exact .refl _
  · exact .step ((Arithmetic.binary_adjacent_iff o d m n e).mpr eq) (.refl _)

end Hypernets.Copying.LambdaEntryOverlap
