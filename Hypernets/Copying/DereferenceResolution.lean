import Hypernets.Copying.Dereference

/-! The arbitrary matched atom tree determines the same store before and after reading. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

/-- Vertex attachments of the preserved atom tree into each rule side. -/
def beforeTreeVertex {h} (T : ContractionTree .atom (h+1)) (d : Nat) : T.net.Vertex → (before T d).Vertex :=
  Net.Expansion.insert (beforeFrame h) (beforeFill T) .tree

def afterTreeVertex {h} (T : ContractionTree .atom (h+1)) (d : Nat) : T.net.Vertex → (after T d).Vertex :=
  Net.Expansion.insert (afterFrame h) (afterFill T) .tree

theorem tree_hop_before {h} (T : ContractionTree .atom (h+1)) (d : Nat) {a b : T.net.Edge}
    (ab : T.net.Adjacent a b) : StoreTrace.Hop (before T d) (beforeTree T d a) (beforeTree T d b) := by
  constructor
  · rcases T.labels a with weak | contr
    · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
    · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
  · obtain ⟨v,ha,hb⟩ := ab
    exact ⟨beforeTreeVertex T d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩

theorem tree_hop_after {h} (T : ContractionTree .atom (h+1)) (d : Nat) {a b : T.net.Edge}
    (ab : T.net.Adjacent a b) : StoreTrace.Hop (after T d) (afterTree T d a) (afterTree T d b) := by
  constructor
  · rcases T.labels a with weak | contr
    · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
    · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
  · obtain ⟨v,ha,hb⟩ := ab
    exact ⟨afterTreeVertex T d v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩

/-- Both sides enter the preserved tree at its first atom input. -/
theorem enters_before {h} (T : ContractionTree .atom (h+1)) (d : Nat) (e : T.net.Edge)
    (entry : Port.input ⟨0,by simp⟩ ∈ T.net.source e) :
    StoreTrace.Hop (before T d) (beforeInstance T d) (beforeTree T d e) := by
  refine ⟨Or.inl rfl,⟨beforeTreeVertex T d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem entry⟩⟩
  change _ ∈ [_]
  exact List.mem_cons_self

theorem enters_after {h} (T : ContractionTree .atom (h+1)) (d : Nat) (e : T.net.Edge)
    (entry : Port.input ⟨0,by simp⟩ ∈ T.net.source e) :
    StoreTrace.Hop (after T d) (afterInstance T d) (afterTree T d e) := by
  refine ⟨Or.inl rfl,⟨afterTreeVertex T d (.input ⟨0,by simp⟩),?_,List.mem_map_of_mem entry⟩⟩
  change _ ∈ [_]
  exact List.mem_cons_self

theorem root_before {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    StoreTrace.Hop (before T d) (beforeTree T d T.root) (beforeStore T d) := by
  constructor
  · rcases T.labels T.root with weak | contr
    · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
    · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
  · refine ⟨beforeTreeVertex T d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
    change _ ∈ [_]; exact List.mem_cons_self

theorem root_after {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    StoreTrace.Hop (after T d) (afterTree T d T.root) (afterStore T d) := by
  constructor
  · rcases T.labels T.root with weak | contr
    · exact Or.inr (Or.inr (congrArg (primitiveLabel d) weak))
    · exact Or.inr (Or.inl (congrArg (primitiveLabel d) contr))
  · refine ⟨afterTreeVertex T d (.output 0),List.mem_map_of_mem T.root_output,?_⟩
    change _ ∈ [_]; exact List.mem_cons_self

/-- Append one relation step without changing the existing trace count. -/
theorem trace_snoc {A : Type} {R : A → A → Prop} {a b c : A} {n}
    (run : Trace R a b n) (last : R b c) : Trace R a c (n+1) := by
  induction run with
  | refl => exact .step last (.refl _)
  | step first tail ih => exact .step first (ih last)

/-- Every arbitrary matched atom tree resolves on both sides, at the same exact cost. -/
theorem resolves_both {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    ∃ n, StoreTrace.Resolves (before T d) (beforeInstance T d) (beforeStore T d) n ∧
      StoreTrace.Resolves (after T d) (afterInstance T d) (afterStore T d) n := by
  obtain ⟨e,n,entry,path⟩ := T.input_reaches_root ⟨0,by simp⟩
  refine ⟨n+2,⟨.step (enters_before T d e entry) ?_,rfl⟩,
    ⟨.step (enters_after T d e entry) ?_,rfl⟩⟩
  · exact trace_snoc (path.map (beforeTree T d) (tree_hop_before T d)) (root_before T d)
  · exact trace_snoc (path.map (afterTree T d) (tree_hop_after T d)) (root_after T d)

/-- The read rewrite preserves exactly the successful atom-resolution count. -/
theorem resolution_count_iff {h} (T : ContractionTree .atom (h+1)) (d n : Nat) :
    StoreTrace.Resolves (before T d) (beforeInstance T d) (beforeStore T d) n ↔
      StoreTrace.Resolves (after T d) (afterInstance T d) (afterStore T d) n := by
  obtain ⟨k,a,b⟩ := resolves_both T d
  constructor
  · intro h; have eq := (StoreTrace.resolves_unique h a).2; subst n; exact b
  · intro h; have eq := (StoreTrace.resolves_unique h b).2; subst n; exact a

/-- No alternative successful lookup before reading can choose another store. -/
theorem store_unique_before {h} (T : ContractionTree .atom (h+1)) (d : Nat) {e n}
    (res : StoreTrace.Resolves (before T d) (beforeInstance T d) e n) : e = beforeStore T d := by
  obtain ⟨k,a,_⟩ := resolves_both T d
  exact (StoreTrace.resolves_unique res a).1

/-- Store identity remains unique after the instance is weakened and the result shared. -/
theorem store_unique_after {h} (T : ContractionTree .atom (h+1)) (d : Nat) {e n}
    (res : StoreTrace.Resolves (after T d) (afterInstance T d) e n) : e = afterStore T d := by
  obtain ⟨k,_,b⟩ := resolves_both T d
  exact (StoreTrace.resolves_unique res b).1
end Hypernets.Copying.Dereference
