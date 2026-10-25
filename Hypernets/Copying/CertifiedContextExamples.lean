import Hypernets.Copying.CertifiedContexts
import Hypernets.Copying.BindingTranslationExamples

set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Examples
open Graph

/-- Two occurrences of the same hole name are not mistaken for one hole.
The inventory counts occurrences, not the set of labels. -/
theorem duplicate_holes_rejected (h : Hole) :
    ¬ SingleHole h (Net.Tensor.net (primitiveNet 0 (.hole h)) (primitiveNet 0 (.hole h))) := by
  rintro ⟨⟨b,e⟩,_,others⟩
  cases b
  · have q := others ⟨true,(0 : Fin 1)⟩ (by intro eq; cases eq)
    exact q h rfl
  · have q := others ⟨false,(0 : Fin 1)⟩ (by intro eq; cases eq)
    exact q h rfl

/-- The nested context has a genuine sole-hole address at its annotated term
interface, even when its representation allowance changes. -/
theorem nestedReferenceContext_certified (d name : Nat) :
    ∃ r, ∃ s : Site (ContextTranslation.graph nestedReferenceContext d name).2 r
      [.term] (environmentInterface 1 0),
      SoleHole s ∧ BindingFree (ContextTranslation.graph nestedReferenceContext d name).2 :=
  SingleHole.context_certificate _ _ _

/-- Packaging the nested example as a certified graph context retains exactly
the old Figure-16 graph, not just an observationally equivalent surrogate. -/
theorem nestedReferenceContext_graph_unchanged (d name : Nat) :
    (ContextTranslation.certified nestedReferenceContext d name).2.graph =
      (ContextTranslation.graph nestedReferenceContext d name).2 := rfl
end Hypernets.Copying.Examples
