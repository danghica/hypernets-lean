import Hypernets.Copying.PrefixReplay

/-! Refocusing for every original reference-identity test, write and read in arbitrary hosts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment.Match
open Graph Search

/-- The pre-head search uses neither the assignment head nor the non-interacting store edge. -/
theorem rooted {d I O} {G : Hypernet d I O} {v i} (m : Assignment.Match G v)
    (root : RootedFrom G i (.rewrite,v)) : RootedFrom m.canonical.1 i m.canonical.2 := by
  apply rooted_of_frames (G := G) (H := m.canonical.1)
    (Net.Replacement.host m.swapped m.headEdge m.filler) id (fun _ _ h => h) rfl rfl ?_ root
  intro n p hist avoid e primitive label active used
  have ne : e ≠ m.headEdge := by
    intro eq; subst e
    exact avoid (uses_visit hist (operation_source m.head.1 m.head.2) used)
  have ns : e ≠ m.storeEdge := by
    intro eq
    exact active.ne_store (primitiveLabel_injective d (label.symm.trans ((congrArg G.edgeLabel eq).trans m.store)))
  refine ⟨.inl ⟨e,ne⟩,label,?_,?_⟩
  · exact List.map_id _
  · change ((m.swapped.target e).map (Net.Replacement.host m.swapped m.headEdge m.filler)).map id = _
    rw [List.map_id,m.swapped_other_target e ne ns]
end Hypernets.Copying.Assignment.Match

namespace Hypernets.Copying.Dereference.Match
open Graph Search

/-- Exchanging the graft's feedback and the store contents changes no other retained target. -/
theorem retained_target {d I O} {G : Hypernet d I O} {v} (m : Dereference.Match G v)
    (e : G.Edge) (ne : e ≠ m.headEdge) (ns : e ≠ m.storeEdge) :
    m.canonical.1.target (.inl ⟨e,ne⟩) = (G.target e).map (Net.Replacement.host G m.headEdge m.filler) := by
  change ((G.target e).map _).map (TargetSwap.exchange m.fresh m.retained) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro x mem
  apply TargetSwap.exchange_other
  · cases x <;> intro eq <;> cases eq
  · intro eq
    have same : x = m.contents := Port.map_injective (fun _ _ h => Sum.inl.inj h) eq
    apply ns
    exact G.target_unique mem (by rw [same,m.storeTarget]; exact List.mem_cons_self)

/-- Every contextual read resumes at a search-rooted token on its actual changed graph. -/
theorem rooted {d I O} {G : Hypernet d I O} {v i} (m : Dereference.Match G v)
    (root : RootedFrom G i (.rewrite,v)) : RootedFrom m.canonical.1 i m.canonical.2 := by
  apply rooted_of_frames (G := G) (H := m.canonical.1)
    (Net.Replacement.host G m.headEdge m.filler) id (fun _ _ h => h) rfl rfl ?_ root
  intro n p hist avoid e primitive label active used
  have ne : e ≠ m.headEdge := by
    intro eq; subst e
    exact avoid (uses_visit hist (operation_source m.head.1 m.head.2) used)
  have ns : e ≠ m.storeEdge := by
    intro eq
    exact active.ne_store (primitiveLabel_injective d (label.symm.trans ((congrArg G.edgeLabel eq).trans m.store)))
  refine ⟨.inl ⟨e,ne⟩,label,?_,?_⟩
  · exact List.map_id _
  · rw [List.map_id,m.retained_target e ne ns]
end Hypernets.Copying.Dereference.Match

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

theorem equality_rooted {d I O} {G H : Hypernet d I O} {v w e i}
    (head : HeadAt G v e (.operation (.binary .atomEq))) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  obtain ⟨b,decision⟩ := rewrite_equality_decision step head
  obtain ⟨iso⟩ := rewrite_equality_canonical step head decision
  exact (iso.rootedFrom i).mp (Search.replacement_rooted head (AtomEquality.filler G e head.1 b) root)

theorem assignment_rooted {d I O} {G H : Hypernet d I O} {v w e i}
    (head : HeadAt G v e (.operation (.binary .assign))) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  obtain ⟨m⟩ := rewrite_assignment_match step head
  obtain ⟨iso⟩ := rewrite_assignment_canonical step m
  exact (iso.rootedFrom i).mp (m.rooted root)

theorem dereference_rooted {d I O} {G H : Hypernet d I O} {v w e i}
    (head : HeadAt G v e (.operation (.unary .deref))) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  obtain ⟨m⟩ := rewrite_dereference_match step head
  obtain ⟨iso⟩ := rewrite_dereference_canonical step m
  exact (iso.rootedFrom i).mp (m.rooted root)
end Hypernets.Copying.Combined
