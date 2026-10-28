import Hypernets.Copying.BindingGuardedReplacement

/-! Guarded replacements may contain arbitrarily deep template holes. Only
shallow holes must be absent; nested binding freedom is proved separately. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CompleteMatchCut
open Graph
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (B : Hypernet d J K)

/-- No shallow inserted hole is needed for the surviving-path argument;
recursive holes inside copied boxes are permitted. -/
theorem guarded_shallow_binding_open (free : ShallowBindingFree G)
    (guard : BindingGuardedOutputs A) (closed : ∀ e, ¬ HoleLabel d (B.edgeLabel e)) :
    ShallowBindingFree (replaceWith f labels B) := by
  intro x y bad source hole path
  have yHost : ∃ b : {e : (net f labels).Edge // e ≠ none}, y = .inl b := by
    cases y with
    | inl b => exact ⟨b,rfl⟩
    | inr b => exact False.elim (closed b hole)
  obtain ⟨b,rfl⟩ := yHost
  rw [survivor_label f labels B] at hole
  obtain ⟨z,first,tail⟩ := path
  obtain ⟨c,rfl,original⟩ := guarded_ancestor_survivor f labels B free guard tail rfl hole
  cases x with
  | inr a => exact guarded_exit_forbidden f labels B free guard first original hole
  | inl a =>
    have src : ∃ v, v ∈ G.source (survivor f labels a) := by
      obtain ⟨v,mem⟩ := source
      obtain ⟨u,mem,_⟩ := List.mem_map.mp mem
      exact ⟨embed f u,survivor_source f labels a mem⟩
    rw [survivor_label f labels B] at bad
    exact free _ _ bad src hole ⟨_,survivor_adjacent f labels B first,original⟩

/-- Admissibility of the actual graft, even with arbitrary holes in its
recursive box bodies. No binding-freedom assumption on the cut is used. -/
theorem bindingFree_replace_open_guarded (free : BindingFree G)
    (guard : BindingGuardedOutputs A) (binding : BindingFree B)
    (closed : ∀ e, ¬ HoleLabel d (B.edgeLabel e)) : BindingFree (replaceWith f labels B) := by
  refine ⟨?_,?_⟩
  · intro e
    cases e with
    | inl e => rw [survivor_label f labels B]; exact free.1 _
    | inr e => exact binding.1 e
  · have shallow := guarded_shallow_binding_open f labels B free.shallow guard closed
    cases d with
    | zero => exact shallow
    | succ d =>
      refine ⟨shallow,?_⟩
      intro e
      cases e with
      | inl e => rw [survivor_label f labels B]; exact free.2.2 _
      | inr e => exact binding.2.2 e

end Hypernets.Copying.CompleteMatchCut
