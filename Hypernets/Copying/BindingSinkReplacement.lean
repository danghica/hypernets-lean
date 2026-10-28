import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.BindingFreeOverlap

/-! Admissibility of replacing a complete sink occurrence. The auxiliary cut
itself need not be binding-free: only the resulting filled graph is proved
admissible. No rootedness or opaque locality condition is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CompleteMatchCut
open Graph

section Geometry
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (B : Hypernet d J K)

/-- A surviving cut edge retains its original host edge occurrence. -/
def survivor (e : {e : (net f labels).Edge // e ≠ none}) : G.Edge :=
  ((retainedEdges f).toFun e).val

theorem survivor_label (e : {e : (net f labels).Edge // e ≠ none}) :
    (replaceWith f labels B).edgeLabel (.inl e) = G.edgeLabel (survivor f labels e) := by
  rcases e with ⟨e,h⟩
  cases e with
  | none => exact False.elim (h rfl)
  | some e => rfl

theorem survivor_source (e : {e : (net f labels).Edge // e ≠ none})
    {v : (net f labels).Vertex} (mem : v ∈ (net f labels).source e.val) :
    embed f v ∈ G.source (survivor f labels e) := by
  rcases e with ⟨e,h⟩
  cases e with
  | none => exact False.elim (h rfl)
  | some e => exact (mem_retainedSource f e v).mp mem

theorem survivor_target (e : {e : (net f labels).Edge // e ≠ none})
    {v : (net f labels).Vertex} (mem : v ∈ (net f labels).target e.val) :
    embed f v ∈ G.target (survivor f labels e) := by
  rcases e with ⟨e,h⟩
  cases e with
  | none => exact False.elim (h rfl)
  | some e => exact (mem_retainedTarget f e v).mp mem

theorem survivor_adjacent {e g : {e : (net f labels).Edge // e ≠ none}}
    (adj : (replaceWith f labels B).Adjacent (.inl e) (.inl g)) :
    G.Adjacent (survivor f labels e) (survivor f labels g) := by
  obtain ⟨v,target,source⟩ := (Net.Replacement.adjacent_host_iff (net f labels) none _ e g).mp adj
  exact ⟨embed f v,survivor_target f labels e target,survivor_source f labels g source⟩

end Geometry
section Sink
variable {d I O J} {A : Hypernet d J []} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (B : Hypernet d J [])

/-- The inserted graph has no output, so no adjacency can leave it. -/
theorem sink_no_exit (a : B.Edge) (e : {e : (net f labels).Edge // e ≠ none}) :
    ¬ (replaceWith f labels B).Adjacent (.inr a) (.inl e) := by
  intro adj
  obtain ⟨v,target,_⟩ := BindingFree.adjacent_insert_host (net f labels) none
    (B.reboundary (hole_input f labels).symm (hole_output f labels).symm) a e adj
  change v ∈ (List.finRange 0).map (outputPort f) at target
  simp at target

/-- Any path ending at a surviving edge consists entirely of surviving edges
and gives an original-host ancestry path. -/
theorem sink_ancestor_survivor {x y : (replaceWith f labels B).Edge}
    (path : Ancestor (replaceWith f labels B) x y)
    {b : {e : (net f labels).Edge // e ≠ none}} (last : y = .inl b) :
    ∃ a : {e : (net f labels).Edge // e ≠ none},
      x = .inl a ∧ Ancestor G (survivor f labels a) (survivor f labels b) := by
  induction path with
  | refl => exact ⟨b,last,.refl _⟩
  | @step x z y adj path ih =>
    obtain ⟨c,rfl,tail⟩ := ih last
    cases x with
    | inl a => exact ⟨a,rfl,.step (survivor_adjacent f labels B adj) tail⟩
    | inr a => exact False.elim (sink_no_exit f labels B a c adj)

/-- A closed sink replacement cannot create a forbidden path to a surviving
hole, even when the temporary cut hole has binding ancestors. -/
theorem sink_shallow_binding (free : ShallowBindingFree G) (closed : HoleFree B) :
    ShallowBindingFree (replaceWith f labels B) := by
  intro x y bad source hole path
  have yHost : ∃ b : {e : (net f labels).Edge // e ≠ none}, y = .inl b := by
    cases y with
    | inl b => exact ⟨b,rfl⟩
    | inr b =>
      obtain ⟨h,eq⟩ := hole
      have no := closed b
      change B.edgeLabel b = primitiveLabel d (.hole h) at eq
      rw [eq] at no
      cases d <;> exact False.elim (no h rfl)
  obtain ⟨b,rfl⟩ := yHost
  obtain ⟨z,first,tail⟩ := path
  obtain ⟨c,rfl,original⟩ := sink_ancestor_survivor f labels B tail rfl
  cases x with
  | inr a => exact sink_no_exit f labels B a c first
  | inl a =>
    have src : ∃ v, v ∈ G.source (survivor f labels a) := by
      obtain ⟨v,mem⟩ := source
      obtain ⟨u,mem,_⟩ := List.mem_map.mp mem
      exact ⟨embed f u,survivor_source f labels a mem⟩
    rw [survivor_label f labels B] at bad hole
    exact free _ _ bad src hole ⟨_,survivor_adjacent f labels B first,original⟩

/-- Replacing a complete sink by a focus-free, hole-free sink preserves the
original observation class. Binding freedom of the cut is not required. -/
theorem bindingFree_replace_sink (free : BindingFree G)
    (focus : FocusFree B) (closed : HoleFree B) : BindingFree (replaceWith f labels B) := by
  refine ⟨?_,?_⟩
  · intro e
    cases e with
    | inl e =>
      rw [survivor_label f labels B]
      exact free.1 _
    | inr e => exact focus e
  · have shallow := sink_shallow_binding f labels B free.shallow closed
    cases d with
    | zero => exact shallow
    | succ d =>
      refine ⟨shallow,?_⟩
      intro e
      cases e with
      | inl e =>
        rw [survivor_label f labels B]
        exact free.2.2 _
      | inr e => exact (BindingFree.paths_of_holeFree (d+1) B closed).2 e

end Sink
end Hypernets.Copying.CompleteMatchCut
