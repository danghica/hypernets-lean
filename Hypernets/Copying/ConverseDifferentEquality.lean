import Hypernets.Copying.EqualityTreeRematch
import Hypernets.Copying.ConverseEqualityTransfer
import Hypernets.Copying.ConverseBindingDescendant

/-! Distinct-store converse equality rematches only the two selected spines,
then constructs actual opposite residuals for the original false-result rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Opening Search.Expansion MatchEmbedding AtomEquality.Different
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {input v}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
include cert free away rooted

/-- Each selected reference spine is downstream of its own original binding
instance; unrelated siblings from either supplied tree remain unrestricted. -/
theorem different_subtrees_avoids {n m k l}
    (U : ContractionTree .atom (n+1)) (V : ContractionTree .atom (m+1))
    (T : ContractionTree .atom (k+1)) (S : ContractionTree .atom (l+1))
    (g : Occurrence (U.atDepth d) (T.atDepth d))
    (j : Occurrence (V.atDepth d) (S.atDepth d))
    (first : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (last : g.ports (.output 0) = .output 0)
    (firstRight : j.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (lastRight : j.ports (.output 0) = .output 0)
    (selected : ∀ e : U.net.Edge, ∃ a n, Port.input ⟨0,by simp⟩ ∈ T.net.source a ∧ Trace T.net.Adjacent a (g.edges e) n)
    (selectedRight : ∀ e : V.net.Edge, ∃ a n, Port.input ⟨0,by simp⟩ ∈ S.net.source a ∧ Trace S.net.Adjacent a (j.edges e) n)
    (f : Occurrence (before T S d) (C.expand R))
    (attached : f.ports (inputPort k l 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C ((TreeRematch.occurrence g j first last firstRight lastRight).comp f).matchEmbedding := by
  have head : HeadAt (C.expand R) (Net.Expansion.host C R v)
      (f.edges (head T S d)) (.operation (.binary .atomEq)) := by
    rw [← attached]; exact f.matchEmbedding.head (head_at T S d)
  have leftAdj : (before T S d).Adjacent (AtomEquality.Different.head T S d) (beforeLeft T S d) :=
    ⟨.internal (.inl (0 : Fin 6)),List.mem_cons_self,List.mem_cons_self⟩
  have rightAdj : (before T S d).Adjacent (AtomEquality.Different.head T S d) (beforeRight T S d) :=
    ⟨.internal (.inl (1 : Fin 6)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩
  have leftBinding : BindingLabel d ((C.expand R).edgeLabel (f.edges (beforeLeft T S d))) := by
    have label : (C.expand R).edgeLabel (f.edges (beforeLeft T S d)) = primitiveLabel d .instanceEdge :=
      f.matchEmbedding.primitive _ _ rfl
    rw [label]; cases d <;> trivial
  have rightBinding : BindingLabel d ((C.expand R).edgeLabel (f.edges (beforeRight T S d))) := by
    have label : (C.expand R).edgeLabel (f.edges (beforeRight T S d)) = primitiveLabel d .instanceEdge :=
      f.matchEmbedding.primitive _ _ rfl
    rw [label]; cases d <;> trivial
  have leftDescendant {e : (before T S d).Edge} (path : Ancestor (before T S d) (beforeLeft T S d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    argument_binding_descendant_not_hole C cert free away rooted head rfl
      (f.matchEmbedding.adjacent leftAdj) leftBinding (path.map f.edges (fun h => f.matchEmbedding.adjacent h))
  have rightDescendant {e : (before T S d).Edge} (path : Ancestor (before T S d) (beforeRight T S d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    argument_binding_descendant_not_hole C cert free away rooted head rfl
      (f.matchEmbedding.adjacent rightAdj) rightBinding (path.map f.edges (fun h => f.matchEmbedding.adjacent h))
  have leftHop {a b : T.net.Edge} (adj : T.net.Adjacent a b) :
      StoreTrace.Hop (before T S d) (beforeLeftTree T S d a) (beforeLeftTree T S d b) := by
    refine ⟨?_,?_⟩
    · rcases T.labels a with weak | contraction
      · exact .inr (.inr (congrArg (primitiveLabel d) weak))
      · exact .inr (.inl (congrArg (primitiveLabel d) contraction))
    · obtain ⟨w,target,source⟩ := adj
      exact ⟨beforeLeftVertex T S d w,List.mem_map_of_mem target,List.mem_map_of_mem source⟩
  have rightHop {a b : S.net.Edge} (adj : S.net.Adjacent a b) :
      StoreTrace.Hop (before T S d) (beforeRightTree T S d a) (beforeRightTree T S d b) := by
    refine ⟨?_,?_⟩
    · rcases S.labels a with weak | contraction
      · exact .inr (.inr (congrArg (primitiveLabel d) weak))
      · exact .inr (.inl (congrArg (primitiveLabel d) contraction))
    · obtain ⟨w,target,source⟩ := adj
      exact ⟨beforeRightVertex T S d w,List.mem_map_of_mem target,List.mem_map_of_mem source⟩
  rintro ⟨part,e⟩ h hole
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact away ⟨_,h,hole,source_owner C R head.2⟩
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact leftDescendant (.refl _) h hole
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact rightDescendant (.refl _) h hole
  · obtain ⟨a,n,entry,path⟩ := selected e
    have enter : StoreTrace.Hop (before T S d) (beforeLeft T S d) (beforeLeftTree T S d a) :=
      ⟨.inl rfl,⟨beforeLeftVertex T S d (.input ⟨0,by simp⟩),List.mem_cons_self,List.mem_map_of_mem entry⟩⟩
    exact leftDescendant (StoreTrace.ancestor (.step enter (path.map (beforeLeftTree T S d) leftHop))) h hole
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    obtain ⟨n,resolve,_⟩ := resolves_left T S d
    exact leftDescendant (StoreTrace.ancestor resolve.1) h hole
  · obtain ⟨a,n,entry,path⟩ := selectedRight e
    have enter : StoreTrace.Hop (before T S d) (beforeRight T S d) (beforeRightTree T S d a) :=
      ⟨.inl rfl,⟨beforeRightVertex T S d (.input ⟨0,by simp⟩),List.mem_cons_self,List.mem_map_of_mem entry⟩⟩
    exact rightDescendant (StoreTrace.ancestor (.step enter (path.map (beforeRightTree T S d) rightHop))) h hole
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    obtain ⟨n,resolve,_⟩ := resolves_right T S d
    exact rightDescendant (StoreTrace.ancestor resolve.1) h hole

end Hypernets.Copying.OperationalTemplates.ConverseOverlap

namespace Hypernets.Copying.OperationalTemplates.ConverseResidual
open Graph Combined RetainedFootprint AtomEquality.Different
variable {kind d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (free : BindingFree C)
    {v : C.Vertex} (away : ¬ Search.Expansion.Entering C (.rewrite,v))
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (rooted : Rooted ⟨C.expand L,(.rewrite,Net.Expansion.host C L v)⟩)
include cert free away rooted

/-- Independently prune both original atom trees while preserving the two
actual stores, their inequality, contents outputs and comparison token. -/
theorem different_occurrence {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (before tree other d) (C.expand R))
    (attached : f.ports (inputPort n m 0) = Net.Expansion.host C R v) :
    ∃ k l, ∃ leftTree : ContractionTree .atom (k+1), ∃ rightTree : ContractionTree .atom (l+1),
      ∃ g : Opening.Occurrence (before leftTree rightTree d) (C.expand R),
        g.ports (inputPort k l 0) = Net.Expansion.host C R v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨k,orientation,g,first,last,a,entry,paths⟩ := tree.minimal_spine d ⟨0,by simp⟩
  obtain ⟨l,otherOrientation,j,firstRight,lastRight,b,otherEntry,otherPaths⟩ := other.minimal_spine d ⟨0,by simp⟩
  let leftTree := ContractionSpine.tree .atom k orientation
  let rightTree := ContractionSpine.tree .atom l otherOrientation
  let leftMap : Opening.Occurrence (leftTree.atDepth d) (tree.atDepth d) := g
  let rightMap : Opening.Occurrence (rightTree.atDepth d) (other.atDepth d) := j
  let matched := (TreeRematch.occurrence leftMap rightMap first last firstRight lastRight).comp f
  refine ⟨k+1,l+1,leftTree,rightTree,matched,attached,?_⟩
  exact ConverseOverlap.different_subtrees_avoids C cert free away rooted leftTree rightTree tree other
    leftMap rightMap first last firstRight lastRight (fun e => ⟨a,e.val,entry,paths e⟩)
    (fun e => ⟨b,e.val,otherEntry,otherPaths e⟩) f attached

include leftClosed rightClosed

/-- Every supplied actual distinct-store equality successor has an actual
left counterpart and an admissible opposite residual, with exact unit cost. -/
theorem different {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (before tree other d) (C.expand R))
    (attached : f.ports (inputPort n m 0) = Net.Expansion.host C R v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) t ∧
      (Specimens.system (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨k,l,leftTree,rightTree,g,token,avoid⟩ := different_occurrence C cert free away rooted tree other f attached
  exact retained_different C cert free leftClosed rightClosed leftTree rightTree g avoid token Q P U step

end Hypernets.Copying.OperationalTemplates.ConverseResidual
