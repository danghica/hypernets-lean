import Hypernets.Copying.BindingSinkRewrite

/-! Complete occurrences whose outputs already lie after binding edges shield
all surviving holes from an inserted closed graph. This is a structural path
criterion, discharged by concrete store-rule footprints below. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Every external output has a sourced binding ancestor inside the graph. -/
def BindingGuardedOutputs {d I O} (A : Hypernet d I O) : Prop :=
  ∀ i : Fin O.length, ∃ e g : A.Edge,
    BindingLabel d (A.edgeLabel e) ∧ (∃ v, v ∈ A.source e) ∧
    Ancestor A e g ∧ Port.output i ∈ A.target g

namespace CompleteMatchCut
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (B : Hypernet d J K)

/-- An inserted-to-surviving crossing followed by a surviving path to a hole
would extend an original sourced binding ancestor to that hole. -/
theorem guarded_exit_forbidden (free : ShallowBindingFree G) (guard : BindingGuardedOutputs A)
    {a : B.Edge} {c b : {e : (net f labels).Edge // e ≠ none}}
    (adj : (replaceWith f labels B).Adjacent (.inr a) (.inl c))
    (tail : Ancestor G (survivor f labels c) (survivor f labels b))
    (hole : HoleLabel d (G.edgeLabel (survivor f labels b))) : False := by
  obtain ⟨v,target,source⟩ := BindingFree.adjacent_insert_host (net f labels) none
    (B.reboundary (hole_input f labels).symm (hole_output f labels).symm) a c adj
  change v ∈ (List.finRange K.length).map (outputPort f) at target
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp target
  obtain ⟨e,g,binding,⟨u,src⟩,path,last⟩ := guard i
  have first : G.Adjacent (f.edges g) (survivor f labels c) := by
    refine ⟨f.ports (.output i),f.target_mem last,?_⟩
    have member := survivor_source f labels c source
    rwa [embed_output] at member
  have positive := (path.map f.edges f.adjacent).append_adjacent first
  obtain ⟨x,first,rest⟩ := positive
  exact free _ _ ((BindingFree.bindingLabel_equiv d (labels e)).mp binding)
    ⟨f.ports u,f.source_mem src⟩ hole ⟨x,first,rest.trans tail⟩

/-- Every path to a surviving hole stays outside a replacement whose original
outputs have binding ancestors; retained adjacencies reflect to the old host. -/
theorem guarded_ancestor_survivor (free : ShallowBindingFree G) (guard : BindingGuardedOutputs A)
    {x y : (replaceWith f labels B).Edge} (path : Ancestor (replaceWith f labels B) x y)
    {b : {e : (net f labels).Edge // e ≠ none}} (last : y = .inl b)
    (hole : HoleLabel d (G.edgeLabel (survivor f labels b))) :
    ∃ a : {e : (net f labels).Edge // e ≠ none},
      x = .inl a ∧ Ancestor G (survivor f labels a) (survivor f labels b) := by
  induction path with
  | refl => exact ⟨b,last,.refl _⟩
  | @step x z y adj path ih =>
    obtain ⟨c,rfl,tail⟩ := ih last
    cases x with
    | inl a => exact ⟨a,rfl,.step (survivor_adjacent f labels B adj) tail⟩
    | inr a => exact False.elim (guarded_exit_forbidden f labels B free guard adj tail hole)

theorem guarded_shallow_binding (free : ShallowBindingFree G) (guard : BindingGuardedOutputs A)
    (closed : HoleFree B) : ShallowBindingFree (replaceWith f labels B) := by
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

/-- A closed replacement of a complete occurrence with guarded outputs
preserves binding freedom of the actual host, including all nested boxes. -/
theorem bindingFree_replace_guarded (free : BindingFree G) (guard : BindingGuardedOutputs A)
    (focus : FocusFree B) (closed : HoleFree B) : BindingFree (replaceWith f labels B) := by
  refine ⟨?_,?_⟩
  · intro e
    cases e with
    | inl e =>
      rw [survivor_label f labels B]
      exact free.1 _
    | inr e => exact focus e
  · have shallow := guarded_shallow_binding f labels B free.shallow guard closed
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

end CompleteMatchCut
end Hypernets.Copying
