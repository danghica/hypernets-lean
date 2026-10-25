import Hypernets.Copying.PaddingPredicates

/-! Composition of separately translated contexts by actual addressed plugging. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace GraphContext
/-- Insert the inner context at the outer context's sole occurrence. -/
noncomputable def compose {r v a d k h e l j}
    (C : GraphContext d k h e l j) (D : GraphContext r v a d k h) :
    GraphContext r v a e l j where
  graph := plugAt C.site D.graph
  site := C.site.comp D.site
  sole := SoleHole.comp C.site D.site C.sole D.sole
  bindingFree := BindingFree.plugAt C.site D.graph
    (SoleHole.sourced C.site C.sole (by decide)) C.bindingFree D.bindingFree

/-- The selected occurrence is the original inner occurrence, even inside boxes. -/
noncomputable def compose_plug_iso {r v a d k h e l j}
    (C : GraphContext d k h e l j) (D : GraphContext r v a d k h)
    (G : Hypernet r [.term] (environmentInterface v a)) :
    DeepIso (plugAt (C.compose D).site G) (plugAt C.site (plugAt D.site G)) :=
  plugAt_assoc C.site D.site G

noncomputable def compose_fill_iso {r v a d k h e l j}
    (C : GraphContext d k h e l j) (D : GraphContext r v a d k h)
    (G : OpenProgram r v a) :
    DeepIso ((C.compose D).fill G).graph (C.fill (D.fill G)).graph :=
  C.compose_plug_iso D G.graph
end GraphContext

namespace TermContext
/-- Composition also preserves the exact maximum/successor depth calculation. -/
theorem depthAt_compose {v a k h l j} (C : TermContext k h l j)
    (D : TermContext v a k h) (d : Nat) :
    (C.compose D).depthAt d = C.depthAt (D.depthAt d) := by
  induction C <;> simp_all [compose,depthAt]
end TermContext

namespace ContextTranslation
/-- Two independently translated contexts compose by actual graph replacement.
The sole addresses work for every graph argument, not only translated terms.
Both original hosts are retained; only the inner host is padded as required by
its occurrence in the outer host. The result has exactly the expected depth. -/
theorem composed_context_filling {v a k h l j}
    (C : TermContext k h l j) (D : TermContext v a k h) (d innerName outerName : Nat) :
    ∃ n m,
    ∃ B : GraphContext (d+n) v a (graph D d innerName).1 k h,
    ∃ A : GraphContext ((graph D d innerName).1+m) k h
        (graph C (graph D d innerName).1 outerName).1 l j,
      B.graph = (graph D d innerName).2 ∧
      A.graph = (graph C (graph D d innerName).1 outerName).2 ∧
      ScopedIso
        ⟨(graph C (graph D d innerName).1 outerName).1,(A.compose (B.pad m)).graph⟩
        (graph (C.compose D) d innerName) ∧
      ∀ G : Hypernet d [.term] (environmentInterface v a),
        ScopedIso
          ⟨(graph C (graph D d innerName).1 outerName).1,
            plugAt (A.compose (B.pad m)).site
              (Translation.pad (d+n) m (Translation.pad d n G))⟩
          (apply (C.compose D) ⟨d,G⟩) := by
  obtain ⟨n,B,hB,lawB⟩ := context_graph_filling D d innerName
  obtain ⟨m,A,hA,lawA⟩ := context_graph_filling C (graph D d innerName).1 outerName
  refine ⟨n,m,B,A,hB,hA,?_,?_⟩
  · have result := lawA B.graph
    rw [hB] at result
    change ScopedIso _ (apply C (graph D d innerName)) at result
    simpa only [graph_compose,GraphContext.compose,GraphContext.pad,hB] using result
  intro G
  have assoc := A.compose_plug_iso (B.pad m)
    (Translation.pad (d+n) m (Translation.pad d n G))
  have commute := plugAt_deepIso A.site
    (Padding.pad_filling B.site (Translation.pad d n G) m).symm
  have first := (ScopedIso.ofIso (assoc.trans commute)).trans
    (lawA (plugAt B.site (Translation.pad d n G)))
  have result := first.trans (apply_iso C (lawB G))
  rwa [← apply_compose] at result

/-- The actual composed graph context reconstructs the unchanged original
translation of the successively filled term. No execution law is required. -/
theorem composed_term_filling {v a k h l j}
    (C : TermContext k h l j) (D : TermContext v a k h)
    (t : Term v a) (innerName outerName : Nat) :
    ∃ n m,
    ∃ B : GraphContext (Translation.depth t+n) v a
        (graph D (Translation.depth t) innerName).1 k h,
    ∃ A : GraphContext ((graph D (Translation.depth t) innerName).1+m) k h
        (graph C (graph D (Translation.depth t) innerName).1 outerName).1 l j,
      B.graph = (graph D (Translation.depth t) innerName).2 ∧
      A.graph = (graph C (graph D (Translation.depth t) innerName).1 outerName).2 ∧
      ScopedIso
        ⟨(graph C (graph D (Translation.depth t) innerName).1 outerName).1,
          plugAt (A.compose (B.pad m)).site
            (Translation.pad (Translation.depth t+n) m
              (Translation.pad (Translation.depth t) n (Translation.term t)))⟩
        (ofTerm (C.fill (D.fill t))) := by
  obtain ⟨n,m,B,A,hB,hA,_,law⟩ := composed_context_filling C D (Translation.depth t) innerName outerName
  refine ⟨n,m,B,A,hB,hA,?_⟩
  have result := law (Translation.term t)
  change ScopedIso _ (apply (C.compose D) (ofTerm t)) at result
  simpa only [apply_ofTerm,TermContext.fill_compose] using result
end ContextTranslation
end Hypernets.Copying
