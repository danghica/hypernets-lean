import Hypernets.Copying.NullaryFootprint
import Hypernets.Copying.ReadTreeRematch
import Hypernets.Copying.AssignmentTreeRematch
import Hypernets.Copying.EqualityTreeRematch
import Hypernets.Copying.TwoInputContractionSubtree

/-! Every selected atom-operation footprint avoids shallow nullary fillings.
The surrounding context is unrestricted; irrelevant original tree branches
are exposed as side inputs of a smaller original rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.NullaryOverlap
open Graph Opening Search.Expansion MatchEmbedding AtomEquality
variable {P : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge P C L R e) (none : P.NoInputs)
    (closed : HoleFree (C.expand L)) {v : C.Vertex}
include cert none closed

/-- An arbitrary selected subtree containing only descendants of the read's
first atom input yields a complete shallow-hole-free read occurrence. -/
theorem read_subtree_avoids {h k} (U : ContractionTree .atom (h+1)) (T : ContractionTree .atom (k+1))
    (g : Occurrence (U.atDepth d) (T.atDepth d))
    (first : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (last : g.ports (.output 0) = .output 0)
    (selected : ∀ e : U.net.Edge, ∃ a n, Port.input ⟨0,by simp⟩ ∈ T.net.source a ∧
      Trace T.net.Adjacent a (g.edges e) n)
    (f : Occurrence (Dereference.before T d) (C.expand L))
    (attached : f.ports (Dereference.inputPort k 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C ((Dereference.TreeRematch.occurrence g first last).comp f).matchEmbedding := by
  have head : HeadAt (C.expand L) (Net.Expansion.host C L v)
      (f.edges (Dereference.localMatch T d).headEdge) (.operation (.unary .deref)) := by
    rw [← attached]; exact f.matchEmbedding.head (Dereference.localMatch T d).head
  have adj : (Dereference.before T d).Adjacent (Dereference.localMatch T d).headEdge (Dereference.beforeInstance T d) :=
    ⟨.internal (.inl (0 : Fin 3)),List.mem_cons_self,List.mem_cons_self⟩
  have descendants {e : (Dereference.before T d).Edge}
      (path : Ancestor (Dereference.before T d) (Dereference.beforeInstance T d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    ancestor_not_hole C cert none closed head.2
      (.step (f.matchEmbedding.adjacent adj) (path.map f.edges (fun h => f.matchEmbedding.adjacent h)))
  rintro ⟨part,e⟩ h hole
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact source_not_hole C cert none closed head.2 h hole
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact descendants (.refl _) h hole
  · obtain ⟨a,n,entry,path⟩ := selected e
    exact descendants (StoreTrace.ancestor (.step (Dereference.enters_before T d a entry)
      (path.map (Dereference.beforeTree T d) (Dereference.tree_hop_before T d)))) h hole
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    obtain ⟨n,resolve,_⟩ := Dereference.resolves_both T d
    exact descendants (StoreTrace.ancestor resolve.1) h hole

/-- The same selected-spine criterion preserves the full stable assignment
value and all of its original outputs. -/
theorem assignment_subtree_avoids {h k J} (U : ContractionTree .atom (h+1)) (T : ContractionTree .atom (k+1))
    (g : Occurrence (U.atDepth d) (T.atDepth d))
    (first : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (last : g.ports (.output 0) = .output 0)
    (selected : ∀ e : U.net.Edge, ∃ a n, Port.input ⟨0,by simp⟩ ∈ T.net.source a ∧
      Trace T.net.Adjacent a (g.edges e) n)
    (G : Hypernet d [.term] J) (stable : Stable G)
    (f : Occurrence (Assignment.before T G) (C.expand L))
    (attached : f.ports (Assignment.inputPort k J 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C ((Assignment.TreeRematch.occurrence g G first last).comp f).matchEmbedding := by
  have head : HeadAt (C.expand L) (Net.Expansion.host C L v)
      (f.edges (Assignment.localMatch T G).headEdge) (.operation (.binary .assign)) := by
    rw [← attached]; exact f.matchEmbedding.head (Assignment.localMatch T G).head
  have adj : (Assignment.before T G).Adjacent (Assignment.localMatch T G).headEdge (Assignment.beforeInstance T G) := by
    cases d
    all_goals exact ⟨.internal (.inl (0 : Fin 4)),List.mem_cons_self,List.mem_cons_self⟩
  have descendants {e : (Assignment.before T G).Edge}
      (path : Ancestor (Assignment.before T G) (Assignment.beforeInstance T G) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    ancestor_not_hole C cert none closed head.2
      (.step (f.matchEmbedding.adjacent adj) (path.map f.edges (fun h => f.matchEmbedding.adjacent h)))
  cases d
  all_goals
    rintro ⟨part,e⟩ h hole
    cases part
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
      exact source_not_hole C cert none closed head.2 h hole
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
      exact descendants (.refl _) h hole
    · obtain ⟨a,n,entry,path⟩ := selected e
      exact descendants (StoreTrace.ancestor (.step (Assignment.enters_before T G a entry)
        (path.map (Assignment.beforeTree T G) (Assignment.tree_hop_before T G)))) h hole
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
      obtain ⟨n,resolve,_⟩ := Assignment.resolves_both T G
      exact descendants (StoreTrace.ancestor resolve.1) h hole
    · have adjacent : (Assignment.before T G).Adjacent (Assignment.localMatch T G).headEdge (Assignment.beforeValue T G e) :=
        ⟨.internal (.inl (1 : Fin 4)),List.mem_cons_of_mem _ List.mem_cons_self,
          List.mem_map_of_mem (Stable.input_source stable.labels e)⟩
      exact ancestor_not_hole C cert none closed head.2 (.step (f.matchEmbedding.adjacent adjacent) (.refl _)) h hole

/-- The complete rematched equality footprint is retained when its atom tree
 contains only descendants of the two evaluated original instances. -/
theorem same_subtree_avoids {h k} (U : ContractionTree .atom (h+2)) (T : ContractionTree .atom (k+2))
    (g : Occurrence (U.atDepth d) (T.atDepth d))
    (first : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (second : g.ports (.input ⟨1,by simp⟩) = .input ⟨1,by simp⟩)
    (last : g.ports (.output 0) = .output 0)
    (selected : ∀ e : U.net.Edge,
      T.FromInput ⟨0,by simp⟩ (g.edges e) ∨ T.FromInput ⟨1,by simp⟩ (g.edges e))
    (f : Occurrence (Same.before T d) (C.expand L))
    (attached : f.ports (Same.inputPort k 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C ((Same.TreeRematch.occurrence g first second last).comp f).matchEmbedding := by
  let compare : (Same.before T d).Edge := ⟨.compare,(0 : Fin 1)⟩
  have head : HeadAt (C.expand L) (Net.Expansion.host C L v)
      (f.edges compare) (.operation (.binary .atomEq)) := by
    rw [← attached]
    exact f.matchEmbedding.head ⟨rfl,List.mem_cons_self⟩
  have adjLeft : (Same.before T d).Adjacent compare (Same.beforeLeft T d) :=
    ⟨.internal (.inl (0 : Fin 5)),List.mem_cons_self,List.mem_cons_self⟩
  have adjRight : (Same.before T d).Adjacent compare (Same.beforeRight T d) :=
    ⟨.internal (.inl (1 : Fin 5)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩
  have leftDescendants {e : (Same.before T d).Edge}
      (path : Ancestor (Same.before T d) (Same.beforeLeft T d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    ancestor_not_hole C cert none closed head.2
      (.step (f.matchEmbedding.adjacent adjLeft) (path.map f.edges (fun h => f.matchEmbedding.adjacent h)))
  have rightDescendants {e : (Same.before T d).Edge}
      (path : Ancestor (Same.before T d) (Same.beforeRight T d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    ancestor_not_hole C cert none closed head.2
      (.step (f.matchEmbedding.adjacent adjRight) (path.map f.edges (fun h => f.matchEmbedding.adjacent h)))
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
    exact source_not_hole C cert none closed head.2 h hole
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

open AtomEquality.Different

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
    (f : Occurrence (before T S d) (C.expand L))
    (attached : f.ports (inputPort k l 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C ((TreeRematch.occurrence g j first last firstRight lastRight).comp f).matchEmbedding := by
  have head : HeadAt (C.expand L) (Net.Expansion.host C L v)
      (f.edges (head T S d)) (.operation (.binary .atomEq)) := by
    rw [← attached]; exact f.matchEmbedding.head (head_at T S d)
  have leftAdj : (before T S d).Adjacent (AtomEquality.Different.head T S d) (beforeLeft T S d) :=
    ⟨.internal (.inl (0 : Fin 6)),List.mem_cons_self,List.mem_cons_self⟩
  have rightAdj : (before T S d).Adjacent (AtomEquality.Different.head T S d) (beforeRight T S d) :=
    ⟨.internal (.inl (1 : Fin 6)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩
  have leftDescendant {e : (before T S d).Edge} (path : Ancestor (before T S d) (beforeLeft T S d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    ancestor_not_hole C cert none closed head.2
      (.step (f.matchEmbedding.adjacent leftAdj) (path.map f.edges (fun h => f.matchEmbedding.adjacent h)))
  have rightDescendant {e : (before T S d).Edge} (path : Ancestor (before T S d) (beforeRight T S d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    ancestor_not_hole C cert none closed head.2
      (.step (f.matchEmbedding.adjacent rightAdj) (path.map f.edges (fun h => f.matchEmbedding.adjacent h)))
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
    exact source_not_hole C cert none closed head.2 h hole
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

open RetainedFootprint

/-- Extract the actual selected atom spine of any original right read, with
all original operation/store attachments and a proved retained footprint. -/
theorem read_occurrence {h} (tree : ContractionTree .atom (h+1))
    (f : Opening.Occurrence (Dereference.before tree d) (C.expand L))
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C L v) :
    ∃ m, ∃ spine : ContractionTree .atom (m+1),
      ∃ g : Opening.Occurrence (Dereference.before spine d) (C.expand L),
        g.ports (Dereference.inputPort m 0) = Net.Expansion.host C L v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := tree.minimal_spine d ⟨0,by simp⟩
  let spine := ContractionSpine.tree .atom n orientation
  let treeMap : Opening.Occurrence (spine.atDepth d) (tree.atDepth d) := g
  let matched := (Dereference.TreeRematch.occurrence treeMap first last).comp f
  refine ⟨n+1,spine,matched,?_,?_⟩
  · exact attached
  · exact read_subtree_avoids C cert none closed spine tree treeMap first last
      (fun e => ⟨a,e.val,entry,paths e⟩) f attached

/-- Selected-spine extraction retains the literal stable assignment value,
its output ordering, the selected store and both value connections. -/
theorem assignment_occurrence {h O} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G)
    (f : Opening.Occurrence (Assignment.before tree G) (C.expand L))
    (attached : f.ports (Assignment.inputPort h O 0) = Net.Expansion.host C L v) :
    ∃ m, ∃ spine : ContractionTree .atom (m+1),
      ∃ g : Opening.Occurrence (Assignment.before spine G) (C.expand L),
        g.ports (Assignment.inputPort m O 0) = Net.Expansion.host C L v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := tree.minimal_spine d ⟨0,by simp⟩
  let spine := ContractionSpine.tree .atom n orientation
  let treeMap : Opening.Occurrence (spine.atDepth d) (tree.atDepth d) := g
  let matched := (Assignment.TreeRematch.occurrence treeMap G first last).comp f
  refine ⟨n+1,spine,matched,?_,?_⟩
  · change f.ports ((Assignment.TreeRematch.occurrence treeMap G first last).ports _) = _
    rw [Assignment.TreeRematch.occurrence_input]
    exact attached
  · exact assignment_subtree_avoids C cert none closed spine tree treeMap first last
      (fun e => ⟨a,e.val,entry,paths e⟩) G stable f attached

/-- Every actual same-store rule supplies a smaller original rule whose
 entire two-selected-input footprint avoids the original shallow holes. -/
theorem same_occurrence {h} (tree : ContractionTree .atom (h+2))
    (f : Opening.Occurrence (AtomEquality.Same.before tree d) (C.expand L))
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C L v) :
    ∃ m, ∃ subtree : ContractionTree .atom (m+2),
      ∃ g : Opening.Occurrence (AtomEquality.Same.before subtree d) (C.expand L),
        g.ports (AtomEquality.Same.inputPort m 0) = Net.Expansion.host C L v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨m,subtree,g,first,second,last,paths⟩ := tree.two_input_subtree d ⟨0,by simp⟩ ⟨1,by simp⟩
    (by intro eq; have := congrArg Fin.val eq; contradiction)
  let matched := (AtomEquality.Same.TreeRematch.occurrence g first second last).comp f
  refine ⟨m,subtree,matched,attached,?_⟩
  exact same_subtree_avoids C cert none closed subtree tree g first second last paths f attached

/-- Independently prune both original atom trees while preserving the two
actual stores, their inequality, contents outputs and comparison token. -/
theorem different_occurrence {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Opening.Occurrence (before tree other d) (C.expand L))
    (attached : f.ports (inputPort n m 0) = Net.Expansion.host C L v) :
    ∃ k l, ∃ leftTree : ContractionTree .atom (k+1), ∃ rightTree : ContractionTree .atom (l+1),
      ∃ g : Opening.Occurrence (before leftTree rightTree d) (C.expand L),
        g.ports (inputPort k l 0) = Net.Expansion.host C L v ∧ AvoidsShallow C g.matchEmbedding := by
  obtain ⟨k,orientation,g,first,last,a,entry,paths⟩ := tree.minimal_spine d ⟨0,by simp⟩
  obtain ⟨l,otherOrientation,j,firstRight,lastRight,b,otherEntry,otherPaths⟩ := other.minimal_spine d ⟨0,by simp⟩
  let leftTree := ContractionSpine.tree .atom k orientation
  let rightTree := ContractionSpine.tree .atom l otherOrientation
  let leftMap : Opening.Occurrence (leftTree.atDepth d) (tree.atDepth d) := g
  let rightMap : Opening.Occurrence (rightTree.atDepth d) (other.atDepth d) := j
  let matched := (TreeRematch.occurrence leftMap rightMap first last firstRight lastRight).comp f
  refine ⟨k+1,l+1,leftTree,rightTree,matched,attached,?_⟩
  exact different_subtrees_avoids C cert none closed leftTree rightTree tree other
    leftMap rightMap first last firstRight lastRight (fun e => ⟨a,e.val,entry,paths e⟩)
    (fun e => ⟨b,e.val,otherEntry,otherPaths e⟩) f attached

end Hypernets.Copying.NullaryOverlap
