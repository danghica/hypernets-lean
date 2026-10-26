import Hypernets.Copying.AtomEquality

/-! Equality distinguishes reference identity by actual store-resolution traces. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality
open Graph

/-- One fixed tree path gives the same successful cost in two graph embeddings. -/
theorem tree_resolution_pair {k d I O J K} (T : ContractionTree .atom k)
    (i : Fin (List.replicate k Wire.atom).length)
    (G : Hypernet d I O) (H : Hypernet d J K)
    (a b : G.Edge) (c e : H.Edge) (f : T.net.Edge → G.Edge) (g : T.net.Edge → H.Edge)
    (forwardG : ∀ {x y}, T.net.Adjacent x y → StoreTrace.Hop G (f x) (f y))
    (forwardH : ∀ {x y}, T.net.Adjacent x y → StoreTrace.Hop H (g x) (g y))
    (enterG : ∀ x, Port.input i ∈ T.net.source x → StoreTrace.Hop G a (f x))
    (enterH : ∀ x, Port.input i ∈ T.net.source x → StoreTrace.Hop H c (g x))
    (exitG : StoreTrace.Hop G (f T.root) b) (exitH : StoreTrace.Hop H (g T.root) e)
    (storeG : G.edgeLabel b = primitiveLabel d .store) (storeH : H.edgeLabel e = primitiveLabel d .store) :
    ∃ n, StoreTrace.Resolves G a b n ∧ StoreTrace.Resolves H c e n := by
  obtain ⟨x,n,src,path⟩ := T.input_reaches_root i
  exact ⟨n+2,⟨.step (enterG x src) (Dereference.trace_snoc (path.map f forwardG) exitG),storeG⟩,
    ⟨.step (enterH x src) (Dereference.trace_snoc (path.map g forwardH) exitH),storeH⟩⟩
namespace Same
def beforeLeftTree {h} (T : ContractionTree .atom (h+2)) (d : Nat) (e : T.net.Edge) : (before T d).Edge := ⟨.tree,e⟩
def beforeLeftVertex {h} (T : ContractionTree .atom (h+2)) (d : Nat) : T.net.Vertex → (before T d).Vertex :=
  Net.Expansion.insert (beforeFrame h) (beforeFill T) .tree
def afterLeftTree {h} (T : ContractionTree .atom (h+2)) (d : Nat) (e : T.net.Edge) : (after T d).Edge := ⟨.tree,e⟩
def afterLeftVertex {h} (T : ContractionTree .atom (h+2)) (d : Nat) : T.net.Vertex → (after T d).Vertex :=
  Net.Expansion.insert (afterFrame h) (afterFill T) .tree
theorem resolves_left {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    ∃ k, StoreTrace.Resolves (before T d) (beforeLeft T d) (beforeStore T d) k ∧
      StoreTrace.Resolves (after T d) (afterLeft T d) (afterStore T d) k := by
  apply tree_resolution_pair T ⟨0,by simp⟩ _ _ _ _ _ _
    (beforeLeftTree T d) (afterLeftTree T d)
  · intro a b hop
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨beforeLeftVertex T d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro a b hop
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨afterLeftVertex T d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro e src
    refine ⟨Or.inl rfl,⟨beforeLeftVertex T d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · intro e src
    refine ⟨Or.inl rfl,⟨afterLeftVertex T d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨beforeLeftVertex T d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨afterLeftVertex T d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · rfl
  · rfl
def beforeRightTree {h} (T : ContractionTree .atom (h+2)) (d : Nat) (e : T.net.Edge) : (before T d).Edge := ⟨.tree,e⟩
def beforeRightVertex {h} (T : ContractionTree .atom (h+2)) (d : Nat) : T.net.Vertex → (before T d).Vertex :=
  Net.Expansion.insert (beforeFrame h) (beforeFill T) .tree
def afterRightTree {h} (T : ContractionTree .atom (h+2)) (d : Nat) (e : T.net.Edge) : (after T d).Edge := ⟨.tree,e⟩
def afterRightVertex {h} (T : ContractionTree .atom (h+2)) (d : Nat) : T.net.Vertex → (after T d).Vertex :=
  Net.Expansion.insert (afterFrame h) (afterFill T) .tree
theorem resolves_right {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    ∃ k, StoreTrace.Resolves (before T d) (beforeRight T d) (beforeStore T d) k ∧
      StoreTrace.Resolves (after T d) (afterRight T d) (afterStore T d) k := by
  apply tree_resolution_pair T ⟨1,by simp⟩ _ _ _ _ _ _
    (beforeRightTree T d) (afterRightTree T d)
  · intro a b hop
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨beforeRightVertex T d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro a b hop
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨afterRightVertex T d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro e src
    refine ⟨Or.inl rfl,⟨beforeRightVertex T d (.input ⟨1,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · intro e src
    refine ⟨Or.inl rfl,⟨afterRightVertex T d (.input ⟨1,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨beforeRightVertex T d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨afterRightVertex T d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · rfl
  · rfl
theorem left_resolution_count_iff {h} (T : ContractionTree .atom (h+2)) (d k : Nat) :
    StoreTrace.Resolves (before T d) (beforeLeft T d) (beforeStore T d) k ↔
      StoreTrace.Resolves (after T d) (afterLeft T d) (afterStore T d) k := by
  obtain ⟨j,a,b⟩ := resolves_left T d
  constructor
  · intro r; have eq := (StoreTrace.resolves_unique r a).2; subst k; exact b
  · intro r; have eq := (StoreTrace.resolves_unique r b).2; subst k; exact a
theorem right_resolution_count_iff {h} (T : ContractionTree .atom (h+2)) (d k : Nat) :
    StoreTrace.Resolves (before T d) (beforeRight T d) (beforeStore T d) k ↔
      StoreTrace.Resolves (after T d) (afterRight T d) (afterStore T d) k := by
  obtain ⟨j,a,b⟩ := resolves_right T d
  constructor
  · intro r; have eq := (StoreTrace.resolves_unique r a).2; subst k; exact b
  · intro r; have eq := (StoreTrace.resolves_unique r b).2; subst k; exact a
end Same
namespace Different
def beforeLeftTree {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (e : T.net.Edge) : (before T U d).Edge := ⟨.tree,e⟩
def beforeLeftVertex {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : T.net.Vertex → (before T U d).Vertex :=
  Net.Expansion.insert (beforeFrame n m) (beforeFill T U) .tree
def afterLeftTree {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (e : T.net.Edge) : (after T U d).Edge := ⟨.tree,e⟩
def afterLeftVertex {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : T.net.Vertex → (after T U d).Vertex :=
  Net.Expansion.insert (afterFrame n m) (afterFill T U) .tree
theorem resolves_left {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    ∃ k, StoreTrace.Resolves (before T U d) (beforeLeft T U d) (beforeStore T U d) k ∧
      StoreTrace.Resolves (after T U d) (afterLeft T U d) (afterStore T U d) k := by
  apply tree_resolution_pair T ⟨0,by simp⟩ _ _ _ _ _ _
    (beforeLeftTree T U d) (afterLeftTree T U d)
  · intro a b hop
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨beforeLeftVertex T U d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro a b hop
    constructor
    · rcases T.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨afterLeftVertex T U d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro e src
    refine ⟨Or.inl rfl,⟨beforeLeftVertex T U d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · intro e src
    refine ⟨Or.inl rfl,⟨afterLeftVertex T U d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨beforeLeftVertex T U d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases T.labels T.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨afterLeftVertex T U d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · rfl
  · rfl
def beforeRightTree {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (e : U.net.Edge) : (before T U d).Edge := ⟨.treeRight,e⟩
def beforeRightVertex {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : U.net.Vertex → (before T U d).Vertex :=
  Net.Expansion.insert (beforeFrame n m) (beforeFill T U) .treeRight
def afterRightTree {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) (e : U.net.Edge) : (after T U d).Edge := ⟨.treeRight,e⟩
def afterRightVertex {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : U.net.Vertex → (after T U d).Vertex :=
  Net.Expansion.insert (afterFrame n m) (afterFill T U) .treeRight
theorem resolves_right {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    ∃ k, StoreTrace.Resolves (before T U d) (beforeRight T U d) (beforeStoreRight T U d) k ∧
      StoreTrace.Resolves (after T U d) (afterRight T U d) (afterStoreRight T U d) k := by
  apply tree_resolution_pair U ⟨0,by simp⟩ _ _ _ _ _ _
    (beforeRightTree T U d) (afterRightTree T U d)
  · intro a b hop
    constructor
    · rcases U.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨beforeRightVertex T U d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro a b hop
    constructor
    · rcases U.labels a with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · obtain ⟨v,ha,hb⟩ := hop
      exact ⟨afterRightVertex T U d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩
  · intro e src
    refine ⟨Or.inl rfl,⟨beforeRightVertex T U d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · intro e src
    refine ⟨Or.inl rfl,⟨afterRightVertex T U d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem src⟩⟩
    change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases U.labels U.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨beforeRightVertex T U d (.output 0),List.mem_map_of_mem U.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · constructor
    · rcases U.labels U.root with weak | contr
      · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
      · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
    · refine ⟨afterRightVertex T U d (.output 0),List.mem_map_of_mem U.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
  · rfl
  · rfl
theorem left_resolution_count_iff {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d k : Nat) :
    StoreTrace.Resolves (before T U d) (beforeLeft T U d) (beforeStore T U d) k ↔
      StoreTrace.Resolves (after T U d) (afterLeft T U d) (afterStore T U d) k := by
  obtain ⟨j,a,b⟩ := resolves_left T U d
  constructor
  · intro r; have eq := (StoreTrace.resolves_unique r a).2; subst k; exact b
  · intro r; have eq := (StoreTrace.resolves_unique r b).2; subst k; exact a
theorem right_resolution_count_iff {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d k : Nat) :
    StoreTrace.Resolves (before T U d) (beforeRight T U d) (beforeStoreRight T U d) k ↔
      StoreTrace.Resolves (after T U d) (afterRight T U d) (afterStoreRight T U d) k := by
  obtain ⟨j,a,b⟩ := resolves_right T U d
  constructor
  · intro r; have eq := (StoreTrace.resolves_unique r a).2; subst k; exact b
  · intro r; have eq := (StoreTrace.resolves_unique r b).2; subst k; exact a
end Different
end Hypernets.Copying.AtomEquality
