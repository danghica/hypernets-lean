import Hypernets.Copying.BindingGuardedReplacement
import Hypernets.Copying.PrimitiveRuleFootprints

/-! Concrete store lookup and equality footprints have sourced binding
ancestors at every output. Their original instance/tree/store resolution
proofs discharge the replacement admissibility criterion. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

theorem StoreTrace.ancestor {d I O} {G : Hypernet d I O} {a b n}
    (trace : Trace (StoreTrace.Hop G) a b n) : Ancestor G a b := by
  induction trace with
  | refl => exact .refl _
  | step first rest ih => exact .step first.2 ih

private theorem instance_source {d I O} {G : Hypernet d I O} {e : G.Edge}
    (label : G.edgeLabel e = primitiveLabel d .instanceEdge) : ∃ v, v ∈ G.source e := by
  have index : 0 < ((alphabet d).signature.input (G.edgeLabel e)).length := by
    rw [label,primitive_input]
    decide
  exact ⟨G.sourcePort e ⟨0,index⟩,G.sourcePort_mem e ⟨0,index⟩⟩

/-- The read output is protected by its consumed instance and its actual
arbitrary atom-tree path to the store. -/
theorem Dereference.before_bindingGuarded {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    BindingGuardedOutputs (Dereference.before T d) := by
  intro i
  have eq : i = (0 : Fin 1) := by
    apply Fin.ext
    have bound := i.isLt
    change i.val < 1 at bound
    change i.val = 0
    omega
  subst i
  obtain ⟨n,before,_⟩ := Dereference.resolves_both T d
  refine ⟨Dereference.beforeInstance T d,Dereference.beforeStore T d,?_,
    instance_source (show (Dereference.before T d).edgeLabel (Dereference.beforeInstance T d) =
      primitiveLabel d .instanceEdge from rfl),StoreTrace.ancestor before.1,?_⟩
  · cases d <;> trivial
  · change Port.output (0 : Fin 1) ∈ [Port.output 0]
    exact List.mem_cons_self

theorem AtomEquality.Same.before_bindingGuarded {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    BindingGuardedOutputs (AtomEquality.Same.before T d) := by
  intro i
  have eq : i = (0 : Fin 1) := by
    apply Fin.ext
    have bound := i.isLt
    change i.val < 1 at bound
    change i.val = 0
    omega
  subst i
  obtain ⟨n,before,_⟩ := AtomEquality.Same.resolves_left T d
  refine ⟨AtomEquality.Same.beforeLeft T d,AtomEquality.Same.beforeStore T d,?_,
    instance_source (show (AtomEquality.Same.before T d).edgeLabel (AtomEquality.Same.beforeLeft T d) =
      primitiveLabel d .instanceEdge from rfl),StoreTrace.ancestor before.1,?_⟩
  · cases d <;> trivial
  · change Port.output (0 : Fin 1) ∈ [Port.output 0]
    exact List.mem_cons_self

/-- Each of the two store outputs has its own original instance ancestor. -/
theorem AtomEquality.Different.before_bindingGuarded {n m}
    (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    BindingGuardedOutputs (AtomEquality.Different.before T U d) := by
  intro i
  have value : i.val = 0 ∨ i.val = 1 := by
    have bound := i.isLt
    change i.val < 2 at bound
    omega
  have eq : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := value.imp Fin.ext Fin.ext
  rcases eq with rfl | rfl
  · obtain ⟨k,before,_⟩ := AtomEquality.Different.resolves_left T U d
    refine ⟨AtomEquality.Different.beforeLeft T U d,AtomEquality.Different.beforeStore T U d,?_,
      instance_source (show (AtomEquality.Different.before T U d).edgeLabel
        (AtomEquality.Different.beforeLeft T U d) = primitiveLabel d .instanceEdge from rfl),
      StoreTrace.ancestor before.1,?_⟩
    · cases d <;> trivial
    · change Port.output (0 : Fin 2) ∈ [Port.output 0]
      exact List.mem_cons_self
  · obtain ⟨k,before,_⟩ := AtomEquality.Different.resolves_right T U d
    refine ⟨AtomEquality.Different.beforeRight T U d,AtomEquality.Different.beforeStoreRight T U d,?_,
      instance_source (show (AtomEquality.Different.before T U d).edgeLabel
        (AtomEquality.Different.beforeRight T U d) = primitiveLabel d .instanceEdge from rfl),
      StoreTrace.ancestor before.1,?_⟩
    · cases d <;> trivial
    · change Port.output (1 : Fin 2) ∈ [Port.output 1]
      exact List.mem_cons_self

namespace Opening.Occurrence
theorem bindingFree_rewrite_guarded {d I O J K} {A B : Hypernet d J K} {G H : Hypernet d I O}
    (f : Occurrence A G) {a : A.Vertex} {b : B.Vertex} {v : H.Vertex}
    (free : BindingFree G) (guard : BindingGuardedOutputs A) (focus : FocusFree B) (closed : HoleFree B)
    (localStep : Rewrite A a B b) (actual : Rewrite G (f.ports a) H v) : BindingFree H := by
  obtain ⟨iso⟩ := f.rewrite_successor localStep actual
  exact (BindingFree.iso_iff iso.graph).mpr
    (CompleteMatchCut.bindingFree_replace_guarded f.matchEmbedding f.label B free guard focus closed)
end Opening.Occurrence

theorem Dereference.rewrite_bindingFree {d I O h} (T : ContractionTree .atom (h+1))
    {G H : Hypernet d I O} (f : Opening.Occurrence (Dereference.before T d) G)
    (free : BindingFree G) {v : H.Vertex}
    (actual : Rewrite G (f.ports (Dereference.inputPort h 0)) H v) : BindingFree H :=
  f.bindingFree_rewrite_guarded free (Dereference.before_bindingGuarded T d)
    (Dereference.focusFree_sides T d).2 (Dereference.holeFree_sides T d).2 (.local (.read T d)) actual

theorem AtomEquality.Same.rewrite_bindingFree {d I O h} (T : ContractionTree .atom (h+2))
    {G H : Hypernet d I O} (f : Opening.Occurrence (AtomEquality.Same.before T d) G)
    (free : BindingFree G) {v : H.Vertex}
    (actual : Rewrite G (f.ports (AtomEquality.Same.inputPort h 0)) H v) : BindingFree H :=
  f.bindingFree_rewrite_guarded free (AtomEquality.Same.before_bindingGuarded T d)
    (AtomEquality.Same.focusFree_sides T d).2 (AtomEquality.Same.holeFree_sides T d).2
    (.local (.same T d)) actual

theorem AtomEquality.Different.rewrite_bindingFree {d I O n m}
    (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1))
    {G H : Hypernet d I O} (f : Opening.Occurrence (AtomEquality.Different.before T U d) G)
    (free : BindingFree G) {v : H.Vertex}
    (actual : Rewrite G (f.ports (AtomEquality.Different.inputPort n m 0)) H v) : BindingFree H :=
  f.bindingFree_rewrite_guarded free (AtomEquality.Different.before_bindingGuarded T U d)
    (AtomEquality.Different.focusFree_sides T U d).2 (AtomEquality.Different.holeFree_sides T U d).2
    (.local (.different T U d)) actual

namespace RetainedFootprint
variable {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding)

/-- Primitive retained footprints have exactly the same labels before
filling, so their concrete output guards remain in the common skeleton. -/
theorem skeleton_bindingGuarded (primitive : BoxPermutation.PrimitiveFootprint A)
    (guard : BindingGuardedOutputs A) : BindingGuardedOutputs (skeleton C f cert avoid) := by
  intro i
  obtain ⟨e,g,binding,source,path,target⟩ := guard i
  refine ⟨e,g,?_,source,Ancestor.map (G := A) (H := skeleton C f cert avoid) (fun e => e) (fun adj => adj) path,target⟩
  obtain ⟨p,label⟩ := primitive e
  have original := (reflect C f.matchEmbedding cert avoid).primitive e p label
  change C.edgeLabel (f.edges e).1 = _ at original
  change BindingLabel d (C.edgeLabel (f.edges e).1)
  rw [original]
  exact label ▸ binding

theorem frame_plug_bindingFree_guarded (B : Hypernet d J K)
    (free : BindingFree C) (primitive : BoxPermutation.PrimitiveFootprint A)
    (guard : BindingGuardedOutputs A) (focus : FocusFree B) (closed : HoleFree B) :
    BindingFree ((frame C f cert avoid).plug none
      (B.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)) :=
  CompleteMatchCut.bindingFree_replace_guarded
    (skeletonOccurrence C f cert avoid).matchEmbedding (skeletonOccurrence C f cert avoid).label
    B free (skeleton_bindingGuarded C f cert avoid primitive guard) focus closed

end RetainedFootprint
end Hypernets.Copying
