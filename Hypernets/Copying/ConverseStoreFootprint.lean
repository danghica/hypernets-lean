import Hypernets.Copying.ReadTreeRematch
import Hypernets.Copying.AssignmentTreeRematch
import Hypernets.Copying.ConverseBindingDescendant

/-! Selected atom spines give complete retained converse read/write footprints.
Unused siblings of an originally supplied tree are not assumed to be retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Opening Search.Expansion MatchEmbedding
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {input v}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
include cert free away rooted

/-- An arbitrary selected subtree containing only descendants of the read's
first atom input yields a complete shallow-hole-free read occurrence. -/
theorem read_subtree_avoids {h k} (U : ContractionTree .atom (h+1)) (T : ContractionTree .atom (k+1))
    (g : Occurrence (U.atDepth d) (T.atDepth d))
    (first : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (last : g.ports (.output 0) = .output 0)
    (selected : ∀ e : U.net.Edge, ∃ a n, Port.input ⟨0,by simp⟩ ∈ T.net.source a ∧
      Trace T.net.Adjacent a (g.edges e) n)
    (f : Occurrence (Dereference.before T d) (C.expand R))
    (attached : f.ports (Dereference.inputPort k 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C ((Dereference.TreeRematch.occurrence g first last).comp f).matchEmbedding := by
  have head : HeadAt (C.expand R) (Net.Expansion.host C R v)
      (f.edges (Dereference.localMatch T d).headEdge) (.operation (.unary .deref)) := by
    rw [← attached]; exact f.matchEmbedding.head (Dereference.localMatch T d).head
  have adj : (Dereference.before T d).Adjacent (Dereference.localMatch T d).headEdge (Dereference.beforeInstance T d) :=
    ⟨.internal (.inl (0 : Fin 3)),List.mem_cons_self,List.mem_cons_self⟩
  have binding : BindingLabel d ((C.expand R).edgeLabel (f.edges (Dereference.beforeInstance T d))) := by
    have label := f.matchEmbedding.primitive (Dereference.beforeInstance T d) .instanceEdge rfl
    change (C.expand R).edgeLabel (f.edges (Dereference.beforeInstance T d)) = _ at label
    rw [label]; cases d <;> trivial
  have descendants {e : (Dereference.before T d).Edge}
      (path : Ancestor (Dereference.before T d) (Dereference.beforeInstance T d) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    argument_binding_descendant_not_hole C cert free away rooted head rfl
      (f.matchEmbedding.adjacent adj) binding (path.map f.edges (fun h => f.matchEmbedding.adjacent h))
  rintro ⟨part,e⟩ h hole
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact away ⟨_,h,hole,source_owner C R head.2⟩
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
    (f : Occurrence (Assignment.before T G) (C.expand R))
    (attached : f.ports (Assignment.inputPort k J 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C ((Assignment.TreeRematch.occurrence g G first last).comp f).matchEmbedding := by
  have head : HeadAt (C.expand R) (Net.Expansion.host C R v)
      (f.edges (Assignment.localMatch T G).headEdge) (.operation (.binary .assign)) := by
    rw [← attached]; exact f.matchEmbedding.head (Assignment.localMatch T G).head
  have adj : (Assignment.before T G).Adjacent (Assignment.localMatch T G).headEdge (Assignment.beforeInstance T G) := by
    cases d
    all_goals exact ⟨.internal (.inl (0 : Fin 4)),List.mem_cons_self,List.mem_cons_self⟩
  have binding : BindingLabel d ((C.expand R).edgeLabel (f.edges (Assignment.beforeInstance T G))) := by
    have original : (Assignment.before T G).edgeLabel (Assignment.beforeInstance T G) = primitiveLabel d .instanceEdge := by cases d <;> rfl
    have label : (C.expand R).edgeLabel (f.edges (Assignment.beforeInstance T G)) = primitiveLabel d .instanceEdge := f.matchEmbedding.primitive _ _ original
    rw [label]; cases d <;> trivial
  have descendants {e : (Assignment.before T G).Edge}
      (path : Ancestor (Assignment.before T G) (Assignment.beforeInstance T G) e) :
      ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) :=
    argument_binding_descendant_not_hole C cert free away rooted head rfl
      (f.matchEmbedding.adjacent adj) binding (path.map f.edges (fun h => f.matchEmbedding.adjacent h))
  cases d
  all_goals
    rintro ⟨part,e⟩ h hole
    cases part
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
      exact away ⟨_,h,hole,source_owner C R head.2⟩
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
      exact adjacent_source_not_hole C cert away rooted head rfl (f.matchEmbedding.adjacent adjacent) h hole

end Hypernets.Copying.OperationalTemplates.ConverseOverlap
