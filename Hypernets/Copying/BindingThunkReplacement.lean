import Hypernets.Copying.BindingStableOutputs
import Hypernets.Copying.OperationalForwardOverlap

/-! Thunk outputs cannot lead to an operational hole through the retained
context: their first consumer is a binding box, while actual operational holes
have term inputs. This extends guarded-output replacement to stable lambdas. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Every shallow hole has the operational families' original single term input. -/
def HoleTermInputs {d I O} (G : Hypernet d I O) : Prop :=
  ∀ e h, G.edgeLabel e = primitiveLabel d (.hole h) → h.input = [.term]

/-- An actual operational filling of a closed expansion cannot leave an
unfilled hole, so every original hole has the family's true input interface. -/
theorem OperationalTemplates.holeTermInputs {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e) (closed : HoleFree (C.expand L)) :
    HoleTermInputs C := by
  intro e h label
  rcases (cert e).origin with copies | ⟨name,eq,pair⟩
  · obtain ⟨copy⟩ := copies.1
    have hole := (copy.primitive (.hole h)).mpr label
    have no := closed ⟨e,copy.edge⟩
    change LabelAll _ d ((L e).edgeLabel copy.edge) at no
    rw [hole] at no
    cases d <;> exact False.elim (no h rfl)
  · have input : (alphabet d).signature.input (C.edgeLabel e) = [.term] := by
      cases pair with
      | witness f pair g => exact pair.input
    rw [label,primitive_input] at input
    exact input

/-- A thunk-consuming edge is a box, unless it is a hole. Operational holes
cannot be that exception. In particular it is a sourced binding edge. -/
theorem thunk_source_binding {d I O} {G : Hypernet d I O} (holes : HoleTermInputs G)
    {e : G.Edge} {v : G.Vertex} {n : Nat} (source : v ∈ G.source e)
    (typed : G.vertexLabel v = .thunk n) :
    BindingLabel d (G.edgeLabel e) ∧ ¬ HoleLabel d (G.edgeLabel e) := by
  have mem := List.mem_map_of_mem (f := G.vertexLabel) source
  rw [typed] at mem
  dsimp only [Net.vertexLabel] at mem
  rw [G.source_typed] at mem
  have primitive (p : Primitive) (label : G.edgeLabel e = primitiveLabel d p) : False := by
    rw [label,primitive_input] at mem
    cases p with
    | hole h => rw [show primitiveSignature.input (.hole h) = h.input from rfl,holes e h label] at mem; simp at mem
    | contraction s => cases s <;> simp [primitiveSignature,ShareSort.wire] at mem
    | operation o => simp [primitiveSignature] at mem
    | _ => simp [primitiveSignature] at mem
  cases d with
  | zero => exact False.elim (primitive (G.edgeLabel e).down rfl)
  | succ d =>
    cases label : G.edgeLabel e with
    | inl p => exact False.elim (primitive p label)
    | inr b => exact ⟨by trivial,by rintro ⟨h,eq⟩; cases eq⟩

namespace CompleteMatchCut
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (B : Hypernet d J K)

/-- Either an original inside guard or the retained thunk consumer prevents
an inserted-to-retained exit from continuing to a surviving operational hole. -/
theorem thunk_exit_forbidden (free : ShallowBindingFree G) (holes : HoleTermInputs G)
    (guard : BindingOrThunkOutputs A) {a : B.Edge} {c b : {e : (net f labels).Edge // e ≠ none}}
    (adj : (replaceWith f labels B).Adjacent (.inr a) (.inl c))
    (tail : Ancestor G (survivor f labels c) (survivor f labels b))
    (hole : HoleLabel d (G.edgeLabel (survivor f labels b))) : False := by
  obtain ⟨v,target,source⟩ := BindingFree.adjacent_insert_host (net f labels) none
    (B.reboundary (hole_input f labels).symm (hole_output f labels).symm) a c adj
  change v ∈ (List.finRange K.length).map (outputPort f) at target
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp target
  have member := survivor_source f labels c source
  rw [embed_output] at member
  rcases guard i with ⟨n,typed⟩ | ⟨e,g,binding,⟨u,src⟩,path,last⟩
  · have type : G.vertexLabel (f.ports (.output i)) = .thunk n :=
      (f.vertexLabel labels (.output i)).trans typed
    obtain ⟨binding,nohole⟩ := thunk_source_binding holes member type
    exact free _ _ binding ⟨_,member⟩ hole
      (tail.positive_of_ne (by intro eq; apply nohole; simpa [eq] using hole))
  · have first : G.Adjacent (f.edges g) (survivor f labels c) :=
      ⟨f.ports (.output i),f.target_mem last,member⟩
    obtain ⟨x,first,rest⟩ := (path.map f.edges f.adjacent).append_adjacent first
    exact free _ _ ((BindingFree.bindingLabel_equiv d (labels e)).mp binding)
      ⟨f.ports u,f.source_mem src⟩ hole ⟨x,first,rest.trans tail⟩

theorem thunk_ancestor_survivor (free : ShallowBindingFree G) (holes : HoleTermInputs G)
    (guard : BindingOrThunkOutputs A) {x y : (replaceWith f labels B).Edge}
    (path : Ancestor (replaceWith f labels B) x y)
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
    | inr a => exact False.elim (thunk_exit_forbidden f labels B free holes guard adj tail hole)

theorem thunk_shallow_binding (free : ShallowBindingFree G) (holes : HoleTermInputs G)
    (guard : BindingOrThunkOutputs A) (closed : HoleFree B) : ShallowBindingFree (replaceWith f labels B) := by
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
  obtain ⟨c,rfl,original⟩ := thunk_ancestor_survivor f labels B free holes guard tail rfl hole
  cases x with
  | inr a => exact thunk_exit_forbidden f labels B free holes guard first original hole
  | inl a =>
    have src : ∃ v, v ∈ G.source (survivor f labels a) := by
      obtain ⟨v,mem⟩ := source
      obtain ⟨u,mem,_⟩ := List.mem_map.mp mem
      exact ⟨embed f u,survivor_source f labels a mem⟩
    rw [survivor_label f labels B] at bad
    exact free _ _ bad src hole ⟨_,survivor_adjacent f labels B first,original⟩

/-- All interfaces of stable allocation and assignment are covered, including
escaping thunk outputs; the actual filled graph, not the cut, is admissible. -/
theorem bindingFree_replace_thunk (free : BindingFree G) (holes : HoleTermInputs G)
    (guard : BindingOrThunkOutputs A) (focus : FocusFree B) (closed : HoleFree B) :
    BindingFree (replaceWith f labels B) := by
  refine ⟨?_,?_⟩
  · intro e
    cases e with
    | inl e => rw [survivor_label f labels B]; exact free.1 _
    | inr e => exact focus e
  · have shallow := thunk_shallow_binding f labels B free.shallow holes guard closed
    cases d with
    | zero => exact shallow
    | succ d =>
      refine ⟨shallow,?_⟩
      intro e
      cases e with
      | inl e => rw [survivor_label f labels B]; exact free.2.2 _
      | inr e => exact (BindingFree.paths_of_holeFree (d+1) B closed).2 e
end CompleteMatchCut

namespace RetainedFootprint
theorem frame_plug_bindingFree_thunk {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (B : Hypernet d J K)
    (free : BindingFree C) (holes : HoleTermInputs C) (primitive : BoxPermutation.PrimitiveFootprint A)
    (guard : BindingOrThunkOutputs A) (focus : FocusFree B) (closed : HoleFree B) :
    BindingFree ((frame C f cert avoid).plug none
      (B.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)) :=
  CompleteMatchCut.bindingFree_replace_thunk
    (skeletonOccurrence C f cert avoid).matchEmbedding (skeletonOccurrence C f cert avoid).label
    B free holes (skeleton_bindingOrThunk C f cert avoid primitive guard) focus closed
end RetainedFootprint
end Hypernets.Copying
