import Hypernets.Copying.TwoInputContractionSubtree
import Hypernets.Copying.EqualityTreeRematch
import Hypernets.Copying.ConverseBindingDescendant
import Hypernets.Copying.ConverseEqualityTransfer

/-! Same-store equality on the converse side uses the union of the two actual
 selected atom paths, and constructs both whole-graph successor and residual. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Opening Search.Expansion MatchEmbedding AtomEquality
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {input v}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
include cert free away rooted

/-- The complete rematched equality footprint is retained when its atom tree
 contains only descendants of the two evaluated original instances. -/
theorem same_subtree_avoids {h k} (U : ContractionTree .atom (h+2)) (T : ContractionTree .atom (k+2))
    (g : Occurrence (U.atDepth d) (T.atDepth d))
    (first : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (second : g.ports (.input ⟨1,by simp⟩) = .input ⟨1,by simp⟩)
    (last : g.ports (.output 0) = .output 0)
    (selected : ∀ e : U.net.Edge,
      T.FromInput ⟨0,by simp⟩ (g.edges e) ∨ T.FromInput ⟨1,by simp⟩ (g.edges e))
    (f : Occurrence (Same.before T d) (C.expand R))
    (attached : f.ports (Same.inputPort k 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C ((Same.TreeRematch.occurrence g first second last).comp f).matchEmbedding := by
  let compare : (Same.before T d).Edge := ⟨.compare,(0 : Fin 1)⟩
  have head : HeadAt (C.expand R) (Net.Expansion.host C R v)
      (f.edges compare) (.operation (.binary .atomEq)) := by
    rw [← attached]
    exact f.matchEmbedding.head ⟨rfl,List.mem_cons_self⟩
  have adjLeft : (Same.before T d).Adjacent compare (Same.beforeLeft T d) :=
    ⟨.internal (.inl (0 : Fin 5)),List.mem_cons_self,List.mem_cons_self⟩
  have adjRight : (Same.before T d).Adjacent compare (Same.beforeRight T d) :=
    ⟨.internal (.inl (1 : Fin 5)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩
  have bindingLeft : BindingLabel d ((C.expand R).edgeLabel (f.edges (Same.beforeLeft T d))) := by
    have label := f.matchEmbedding.primitive (Same.beforeLeft T d) .instanceEdge rfl
    change (C.expand R).edgeLabel (f.edges (Same.beforeLeft T d)) = _ at label
    rw [label]; cases d <;> trivial
  have bindingRight : BindingLabel d ((C.expand R).edgeLabel (f.edges (Same.beforeRight T d))) := by
    have label := f.matchEmbedding.primitive (Same.beforeRight T d) .instanceEdge rfl
    change (C.expand R).edgeLabel (f.edges (Same.beforeRight T d)) = _ at label
    rw [label]; cases d <;> trivial
  have leftDescendants {e : (Same.before T d).Edge}
      (path : Ancestor (Same.before T d) (Same.beforeLeft T d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    argument_binding_descendant_not_hole C cert free away rooted head rfl
      (f.matchEmbedding.adjacent adjLeft) bindingLeft (path.map f.edges (fun h => f.matchEmbedding.adjacent h))
  have rightDescendants {e : (Same.before T d).Edge}
      (path : Ancestor (Same.before T d) (Same.beforeRight T d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    argument_binding_descendant_not_hole C cert free away rooted head rfl
      (f.matchEmbedding.adjacent adjRight) bindingRight (path.map f.edges (fun h => f.matchEmbedding.adjacent h))
  have treePath {a b n} (path : Trace T.net.Adjacent a b n) :
      Ancestor (Same.before T d) (Same.beforeLeftTree T d a) (Same.beforeLeftTree T d b) := by
    induction path with
    | refl a => exact .refl _
    | step adj path ih =>
      obtain ⟨w,hw,kw⟩ := adj
      exact .step ⟨Same.beforeLeftVertex T d w,List.mem_map_of_mem hw,List.mem_map_of_mem kw⟩ ih
  rintro ⟨part,e⟩ h hole
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact away ⟨_,h,hole,source_owner C R head.2⟩
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact leftDescendants (.refl _) h hole
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact rightDescendants (.refl _) h hole
  · rcases selected e with ⟨a,n,entry,path⟩ | ⟨a,n,entry,path⟩
    · apply leftDescendants (.step ?_ (treePath path)) h hole
      refine ⟨Same.beforeLeftVertex T d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem entry⟩
      change _ ∈ [_]; exact List.mem_cons_self
    · apply rightDescendants (.step ?_ (treePath path)) h hole
      refine ⟨Same.beforeLeftVertex T d (.input ⟨1,by simp⟩),?_,List.mem_map_of_mem entry⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    obtain ⟨n,resolve,_⟩ := Same.resolves_left T d
    exact leftDescendants (StoreTrace.ancestor resolve.1) h hole

end Hypernets.Copying.OperationalTemplates.ConverseOverlap

namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert free away rooted

/-- Every actual right same-store rule supplies a smaller original rule whose
 entire two-selected-input footprint avoids the original shallow holes. -/
theorem same_occurrence {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand R))
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C R v) :
    ∃ m, ∃ subtree : ContractionTree .atom (m+2),
      ∃ g : Opening.Occurrence (AtomEquality.Same.before subtree d) (C.expand R),
        g.ports (AtomEquality.Same.inputPort m 0) = Net.Expansion.host C R v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨m,subtree,g,first,second,last,paths⟩ := tree.two_input_subtree d ⟨0,by simp⟩ ⟨1,by simp⟩
    (by intro eq; have := congrArg Fin.val eq; contradiction)
  let matched := (AtomEquality.Same.TreeRematch.occurrence g first second last).comp f
  refine ⟨m,subtree,matched,attached,?_⟩
  exact ConverseOverlap.same_subtree_avoids C cert free away rooted subtree tree g first second last paths f attached

include leftClosed rightClosed

/-- Quantitative converse same-store equality for every independently supplied
 actual right successor, with an admissible opposite original quasi-specimen. -/
theorem same {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand R))
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨m,subtree,g,token,avoid⟩ := same_occurrence C cert free away rooted tree f attached
  exact retained_same C cert free leftClosed rightClosed subtree g avoid token Q P U step

end Hypernets.Copying.OperationalTemplates.ConverseResidual
