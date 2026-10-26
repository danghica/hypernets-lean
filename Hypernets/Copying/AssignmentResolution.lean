import Hypernets.Copying.Assignment

/-! The arbitrary matched atom tree determines the same store before and after assignment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

/-- Original tree edges retain their identities on each rule side. -/
def beforeTree {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : T.net.Edge) : (before T G).Edge := by
  cases d <;> exact ⟨.tree,e⟩
def afterTree {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : T.net.Edge) : (after T G).Edge := by
  cases d <;> exact ⟨.tree,e⟩
def beforeTreeVertex {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : T.net.Vertex → (before T G).Vertex := by
  cases d <;> exact Net.Expansion.insert (beforePattern _ h O) (beforeFill T G) .tree
def afterTreeVertex {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : T.net.Vertex → (after T G).Vertex := by
  cases d <;> exact Net.Expansion.insert (afterPattern _ h O) (afterFill T G) .tree

theorem tree_labels {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : T.net.Edge) :
    (before T G).edgeLabel (beforeTree T G e) = primitiveLabel d (T.net.edgeLabel e) ∧
    (after T G).edgeLabel (afterTree T G e) = primitiveLabel d (T.net.edgeLabel e) := by cases d <;> exact ⟨rfl,rfl⟩

theorem tree_hop_before {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) {a b : T.net.Edge}
    (ab : T.net.Adjacent a b) : StoreTrace.Hop (before T G) (beforeTree T G a) (beforeTree T G b) := by
  cases d
  all_goals
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (by rw [(tree_labels T G a).1,weak]))
      · exact Or.inr (Or.inl (by rw [(tree_labels T G a).1,contr]))
    · obtain ⟨v,ha,hb⟩ := ab
      exact ⟨beforeTreeVertex T G v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩

theorem tree_hop_after {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) {a b : T.net.Edge}
    (ab : T.net.Adjacent a b) : StoreTrace.Hop (after T G) (afterTree T G a) (afterTree T G b) := by
  cases d
  all_goals
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (by rw [(tree_labels T G a).2,weak]))
      · exact Or.inr (Or.inl (by rw [(tree_labels T G a).2,contr]))
    · obtain ⟨v,ha,hb⟩ := ab
      exact ⟨afterTreeVertex T G v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩

/-- Both sides enter the preserved tree at its first atom input. -/
theorem enters_before {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : T.net.Edge)
    (entry : Port.input ⟨0,by simp⟩ ∈ T.net.source e) :
    StoreTrace.Hop (before T G) (beforeInstance T G) (beforeTree T G e) := by
  cases d
  all_goals
    refine ⟨Or.inl rfl,⟨beforeTreeVertex T G (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem entry⟩⟩
    change _ ∈ [_]
    exact List.mem_cons_self

theorem enters_after {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : T.net.Edge)
    (entry : Port.input ⟨0,by simp⟩ ∈ T.net.source e) :
    StoreTrace.Hop (after T G) (afterInstance T G) (afterTree T G e) := by
  cases d
  all_goals
    refine ⟨Or.inl rfl,⟨afterTreeVertex T G (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem entry⟩⟩
    change _ ∈ [_]
    exact List.mem_cons_self

theorem root_before {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    StoreTrace.Hop (before T G) (beforeTree T G T.root) (beforeStore T G) := by
  cases d
  all_goals
    constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (by rw [(tree_labels T G T.root).1,weak]))
      · exact Or.inr (Or.inl (by rw [(tree_labels T G T.root).1,contr]))
    · refine ⟨beforeTreeVertex T G (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self

theorem root_after {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    StoreTrace.Hop (after T G) (afterTree T G T.root) (afterStore T G) := by
  cases d
  all_goals
    constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (by rw [(tree_labels T G T.root).2,weak]))
      · exact Or.inr (Or.inl (by rw [(tree_labels T G T.root).2,contr]))
    · refine ⟨afterTreeVertex T G (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self

/-- Every arbitrary matched atom tree resolves on both sides, at the same exact cost. -/
theorem resolves_both {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    ∃ n, StoreTrace.Resolves (before T G) (beforeInstance T G) (beforeStore T G) n ∧
      StoreTrace.Resolves (after T G) (afterInstance T G) (afterStore T G) n := by
  obtain ⟨e,n,entry,path⟩ := T.input_reaches_root ⟨0,by simp⟩
  refine ⟨n+2,⟨.step (enters_before T G e entry) ?_,(store_labels T G).1⟩,
    ⟨.step (enters_after T G e entry) ?_,(store_labels T G).2⟩⟩
  · exact Dereference.trace_snoc (path.map (beforeTree T G) (tree_hop_before T G)) (root_before T G)
  · exact Dereference.trace_snoc (path.map (afterTree T G) (tree_hop_after T G)) (root_after T G)

/-- The assignment rewrite preserves exactly the successful atom-resolution count. -/
theorem resolution_count_iff {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (n : Nat) :
    StoreTrace.Resolves (before T G) (beforeInstance T G) (beforeStore T G) n ↔
      StoreTrace.Resolves (after T G) (afterInstance T G) (afterStore T G) n := by
  obtain ⟨k,a,b⟩ := resolves_both T G
  constructor
  · intro h; have eq := (StoreTrace.resolves_unique h a).2; subst n; exact b
  · intro h; have eq := (StoreTrace.resolves_unique h b).2; subst n; exact a

/-- No alternative successful lookup before assignment can choose another store. -/
theorem store_unique_before {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) {e n}
    (res : StoreTrace.Resolves (before T G) (beforeInstance T G) e n) : e = beforeStore T G := by
  obtain ⟨k,a,_⟩ := resolves_both T G
  exact (StoreTrace.resolves_unique res a).1

/-- Store identity remains unique after the instance is weakened and the store updated. -/
theorem store_unique_after {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) {e n}
    (res : StoreTrace.Resolves (after T G) (afterInstance T G) e n) : e = afterStore T G := by
  obtain ⟨k,_,b⟩ := resolves_both T G
  exact (StoreTrace.resolves_unique res b).1
end Hypernets.Copying.Assignment
