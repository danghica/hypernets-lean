import Hypernets.Copying.ContextualRobustness

/-! The addressed bridge for the original term-context translation. -/
namespace Hypernets.Copying
open Graph Combined

namespace ContextTranslation
/-- A translated closing term context has a genuine original closing address,
with its original graph and exact padded filling law. Bound variables in the
hole's scope are retained. -/
theorem closing_context {v a} (C : TermContext v a 0 0) (d name : Nat) :
    ∃ n, ∃ D : ClosingContext (d+n) v a,
      D.depth = (graph C d name).1 ∧
      (∃ eq : D.depth = (graph C d name).1, eq ▸ D.graph = (graph C d name).2) ∧
      ∀ A : Hypernet d [.term] (environmentInterface v a),
        ScopedIso (k := 0) (h := 0) ⟨D.depth,D.fill (Translation.pad d n A)⟩ (apply C ⟨d,A⟩) := by
  obtain ⟨n,D,same,law⟩ := context_graph_filling C d name
  exact ⟨n,⟨_,D.graph,D.site,D.sole,D.bindingFree⟩,rfl,⟨rfl,same⟩,law⟩

/-- Paired filling certificates cover translated closing contexts, including
holes nested beneath binders. Their reconstruction law uses the actual
Figure 16 graph, without a new term interpretation. -/
theorem closing_specimens (T : PreTemplate) (closed : T.OutputClosed)
    {v a} (C : TermContext v a 0 0) (d name : Nat) :
    ∃ n, ∃ D : ClosingContext (d+n) v a,
      (∀ A : Hypernet d [.term] (environmentInterface v a),
        ScopedIso (k := 0) (h := 0) ⟨D.depth,D.fill (Translation.pad d n A)⟩ (apply C ⟨d,A⟩)) ∧
      ∀ G H : OpenProgram d v a, T.Rel (G.pad n).graph (H.pad n).graph →
        (Specimens.system T Specimens.bindingFreeContexts closed).Lifting
          (StateClass.execution.initial (D.close (G.pad n)))
          (StateClass.execution.initial (D.close (H.pad n))) := by
  obtain ⟨n,D,_,_,law⟩ := closing_context C d name
  exact ⟨n,D,law,fun G H rel => Specimens.closing_initial_lifting T closed D _ _ rel⟩
end ContextTranslation

namespace Specimens
/-- It suffices to prove membership at arbitrarily large common allowances.
Exact padding reflection discharges the change of allowance, so this result
does not impose an extra depth-stability axiom on the template. -/
theorem term_equiv_cofinal (T : PreTemplate) (closed : T.OutputClosed)
    (safe : (system T bindingFreeContexts closed).InputSafe CostOrder.any CostOrder.improvement)
    (robust : (system T bindingFreeContexts closed).Robust CostOrder.any CostOrder.improvement CostOrder.any)
    (robustConverse : (system T bindingFreeContexts closed).opposite.Robust CostOrder.any CostOrder.improvement CostOrder.any)
    {k h} (t u : Term k h)
    (related : ∀ b, ∃ N, b ≤ N ∧ ∃ ht : Translation.depth t ≤ N, ∃ hu : Translation.depth u ≤ N,
      T.Rel (translatedProgram t N ht).graph (translatedProgram u N hu).graph) :
    ObservationalEquiv Combined.execution t u := by
  apply (Combined.observationalEquiv_iff_cofinal t u).mpr
  intro b
  obtain ⟨N,bN,ht,hu,rel⟩ := related b
  exact ⟨N,bN,ht,hu,contextual_equiv T closed CostOrder.reasonable_termination
    safe safe robust robustConverse _ _ rel⟩

/-- Template reasoning composes with every original term context, including
unequal translation depths and enclosing binders. All execution isomorphism,
padding and context-composition laws have already been proved concretely. -/
theorem term_context_equiv (T : PreTemplate) (closed : T.OutputClosed)
    (safe : (system T bindingFreeContexts closed).InputSafe CostOrder.any CostOrder.improvement)
    (robust : (system T bindingFreeContexts closed).Robust CostOrder.any CostOrder.improvement CostOrder.any)
    (robustConverse : (system T bindingFreeContexts closed).opposite.Robust CostOrder.any CostOrder.improvement CostOrder.any)
    {v a k h} (C : TermContext v a k h) (t u : Term v a)
    (related : ∀ d (ht : Translation.depth t ≤ d) (hu : Translation.depth u ≤ d),
      T.Rel (translatedProgram t d ht).graph (translatedProgram u d hu).graph) :
    ObservationalEquiv Combined.execution (C.fill t) (C.fill u) :=
  Combined.observationalEquiv_context C t u (term_equiv T closed safe robust robustConverse t u related)
end Specimens
end Hypernets.Copying
