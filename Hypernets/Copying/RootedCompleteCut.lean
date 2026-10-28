import Hypernets.Copying.RootedBindingBarrier
import Hypernets.Copying.BindingThunkReplacement

/-! A complete cut is admissible when its input ports are actually rooted
term positions and its outputs are guarded or thunk-typed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CompleteMatchCut
open Graph Search
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))

/-- Retained-to-retained cut adjacency is literally old-host adjacency. -/
theorem cut_adjacent {a b : RetainedEdge f} (adj : (net f labels).Adjacent (some a) (some b)) :
    G.Adjacent a.val b.val := by
  obtain ⟨v,t,s⟩ := adj
  exact ⟨embed f v,(mem_retainedTarget f a v).mp t,(mem_retainedSource f b v).mp s⟩

/-- A cut exit cannot continue along retained edges to an original hole. -/
theorem cut_exit_hole (free : ShallowBindingFree G) (holes : HoleTermInputs G)
    (guard : BindingOrThunkOutputs A) {a b : RetainedEdge f}
    (adj : (net f labels).Adjacent none (some a)) (path : Ancestor G a.val b.val)
    (hole : HoleLabel d (G.edgeLabel b.val)) : False := by
  obtain ⟨v,t,s⟩ := adj
  obtain ⟨i,rfl⟩ := (mem_hole_target f v).mp t
  have src := (mem_retainedSource f a _).mp s
  rw [embed_output] at src
  rcases guard i with ⟨n,type⟩ | ⟨e,g,binding,source,path',last⟩
  · obtain ⟨binding,nohole⟩ := thunk_source_binding holes src ((f.vertexLabel labels _).trans type)
    exact free _ _ binding ⟨_,src⟩ hole
      (path.positive_of_ne (by intro eq; exact nohole (eq ▸ hole)))
  · obtain ⟨u,source⟩ := source
    have first : G.Adjacent (f.edges g) a.val := ⟨_,f.target_mem last,src⟩
    obtain ⟨x,head,tail⟩ := (path'.map f.edges f.adjacent).append_adjacent first
    exact free _ _ ((BindingFree.bindingLabel_equiv d (labels e)).mp binding)
      ⟨_,f.source_mem source⟩ hole ⟨x,head,tail.trans path⟩

/-- Backwards from a surviving hole, the cut's new edge cannot occur. -/
theorem cut_ancestor_hole (free : ShallowBindingFree G) (holes : HoleTermInputs G)
    (guard : BindingOrThunkOutputs A) {x y : (net f labels).Edge}
    (path : Ancestor (net f labels) x y) {b : RetainedEdge f} (last : y = some b)
    (hole : HoleLabel d (G.edgeLabel b.val)) :
    ∃ a : RetainedEdge f, x = some a ∧ Ancestor G a.val b.val := by
  induction path with
  | refl => exact ⟨b,last,.refl _⟩
  | @step x z y adj path ih =>
    obtain ⟨c,rfl,tail⟩ := ih last
    cases x with
    | none => exact False.elim (cut_exit_hole f labels free holes guard adj tail hole)
    | some a => exact ⟨a,rfl,.step (cut_adjacent f labels adj) tail⟩

/-- A retained predecessor of the cut produces an original matched input. -/
theorem cut_into {a : RetainedEdge f} (adj : (net f labels).Adjacent (some a) none) :
    ∃ i, f.ports (.input i) ∈ G.target a.val := by
  obtain ⟨v,t,s⟩ := adj
  obtain ⟨i,rfl⟩ := (mem_hole_source f v).mp s
  exact ⟨i,by simpa only [embed_input] using (mem_retainedTarget f a _).mp t⟩

variable (reach : ∀ i, OperationReachable G (f.ports (.input i)))
    (terms : ∀ i : Fin J.length, J[i] = .term) (guard : BindingOrThunkOutputs A)
    (holes : HoleTermInputs G)
include reach terms guard holes

omit terms in
/-- A cut exit cannot return along retained edges to any of its rooted inputs. -/
theorem cut_exit_input {a : RetainedEdge f} {g : G.Edge} {j}
    (adj : (net f labels).Adjacent none (some a))
    (path : Ancestor G a.val g) (target : f.ports (.input j) ∈ G.target g) : False := by
  obtain ⟨v,t,s⟩ := adj
  obtain ⟨i,rfl⟩ := (mem_hole_target f v).mp t
  have src := (mem_retainedSource f a _).mp s
  rw [embed_output] at src
  rcases guard i with ⟨n,type⟩ | ⟨e,g',binding,source,path',last⟩
  · have binding := (thunk_source_binding holes src ((f.vertexLabel labels _).trans type)).1
    exact (reach j).no_binding_ancestor binding path target
  · have first : G.Adjacent (f.edges g') a.val := ⟨_,f.target_mem last,src⟩
    exact (reach j).no_binding_ancestor ((BindingFree.bindingLabel_equiv d (labels e)).mp binding)
      ((path'.map f.edges f.adjacent).trans (.step first path)) target

omit holes in
/-- The auxiliary cut has no self-loop: either typing or an original binding
ancestor would contradict its rooted term input. -/
theorem cut_no_loop : ¬ (net f labels).Adjacent none none := by
  rintro ⟨v,t,s⟩
  obtain ⟨i,hi⟩ := (mem_hole_target f v).mp t
  obtain ⟨j,hj⟩ := (mem_hole_source f v).mp s
  have eq : f.ports (.output i) = f.ports (.input j) := by
    have e := congrArg (embed f) (hi.trans hj.symm)
    simpa only [embed_input,embed_output] using e
  rcases guard i with ⟨n,type⟩ | ⟨e,g,binding,source,path,last⟩
  · have typed := (f.vertexLabel labels (.output i)).trans type
    rw [eq,f.vertexLabel labels (.input j)] at typed
    exact Wire.noConfusion ((terms j).symm.trans typed)
  · exact (reach j).no_binding_ancestor ((BindingFree.bindingLabel_equiv d (labels e)).mp binding)
      (path.map f.edges f.adjacent) (eq ▸ f.target_mem last)

/-- An ancestry ending at the cut is either reflexive there, or has a
retained prefix ending at an original input producer. -/
theorem cut_ancestor_input {x y : (net f labels).Edge} (path : Ancestor (net f labels) x y)
    (last : y = none) : x = none ∨ ∃ a : RetainedEdge f, ∃ g i,
      x = some a ∧ Ancestor G a.val g ∧ f.ports (.input i) ∈ G.target g := by
  induction path with
  | refl => exact .inl last
  | @step x z y adj path ih =>
    rcases ih last with rfl | ⟨a,g,i,rfl,tail,target⟩
    · cases x with
      | none => exact False.elim (cut_no_loop f labels reach terms guard adj)
      | some a =>
        obtain ⟨i,target⟩ := cut_into f labels adj
        exact .inr ⟨a,a.val,i,rfl,.refl _,target⟩
    · cases x with
      | none => exact False.elim (cut_exit_input f labels reach guard holes adj tail target)
      | some b => exact .inr ⟨b,g,i,rfl,.step (cut_adjacent f labels adj) tail,target⟩

/-- Rooted inputs and protected outputs make the actual complete cut
binding-free; no locality or cut-admissibility law is assumed. -/
theorem bindingFree_cut (free : BindingFree G) : BindingFree (net f labels) := by
  have shallow : ShallowBindingFree (net f labels) := by
    intro x y binding source hole ⟨z,first,tail⟩
    cases y with
    | some b =>
      obtain ⟨a,rfl,path⟩ := cut_ancestor_hole f labels free.shallow holes guard tail rfl hole
      cases x with
      | none => exact cut_exit_hole f labels free.shallow holes guard first path hole
      | some c =>
        obtain ⟨v,src⟩ := source
        exact free.shallow c.val b.val binding ⟨_,(mem_retainedSource f c _).mp src⟩ hole
          ⟨_,cut_adjacent f labels first,path⟩
    | none =>
      rcases cut_ancestor_input f labels reach terms guard holes tail rfl with rfl | ⟨a,g,i,rfl,path,target⟩
      · cases x with
        | none => exact cut_no_loop f labels reach terms guard first
        | some a =>
          obtain ⟨i,target⟩ := cut_into f labels first
          exact (reach i).no_binding_ancestor binding (.refl _) target
      · cases x with
        | none => exact cut_exit_input f labels reach guard holes first path target
        | some b => exact (reach i).no_binding_ancestor binding (.step (cut_adjacent f labels first) path) target
  refine ⟨?_,?_⟩
  · intro e
    cases e with
    | none => cases d <;> intro m eq <;> cases eq
    | some e => exact free.1 e.val
  · cases d with
    | zero => exact shallow
    | succ d =>
      refine ⟨shallow,?_⟩
      intro e
      cases e with
      | none => trivial
      | some e => exact free.2.2 e.val

end Hypernets.Copying.CompleteMatchCut
