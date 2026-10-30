import Hypernets.Copying.BoxPullContractionLaws
import Hypernets.Copying.NullaryFootprint
import Hypernets.Copying.ConverseFillings
import Hypernets.Copying.PrimitiveRuleFootprints

/-! A sourced primitive footprint cannot enter a shallow BPullC replacement:
its original interface consists of a thunk wire, while every nonhole primitive
accepts only term or atom wires. This applies in unrestricted contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Search.Expansion

/-- Both actual endpoints retain the paper's single thunk input. -/
theorem UpToIso.inputs_thunk {d I O} {G H : Hypernet d I O} (pair : UpToIso G H)
    (i : Fin I.length) : ∃ n, I[i] = .thunk n := by
  cases pair with
  | witness _ step _ =>
    cases step with
    | @pull d n k h s B free =>
      have eq : i = 0 := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
      subst i
      exact ⟨n,rfl⟩

/-- None of the original primitive operation/store/sharing rules has a
thunk input; primitive holes are the sole excluded constructor. -/
theorem primitive_input_not_thunk (p : Primitive) (nonhole : ∀ h, p ≠ .hole h) (n : Nat) :
    Wire.thunk n ∉ primitiveSignature.input p := by
  cases p with
  | operation o => simp [primitiveSignature]
  | contraction s => cases s <;> simp [primitiveSignature,ShareSort.wire]
  | weakening s => simp [primitiveSignature]
  | instanceEdge => simp [primitiveSignature]
  | store => simp [primitiveSignature]
  | focus m => simp [primitiveSignature]
  | hole h => exact False.elim (nonhole h rfl)

/-- A thunk-typed external input cannot be the source of a nonhole primitive. -/
theorem primitive_no_thunk_source {d I O} (G : Hypernet d I O) (e : G.Edge) (p : Primitive)
    (label : G.edgeLabel e = primitiveLabel d p) (nonhole : ∀ h, p ≠ .hole h)
    (i : Fin I.length) (n : Nat) (typed : I[i] = .thunk n) :
    Port.input i ∉ G.source e := by
  intro source
  have mem : G.vertexLabel (.input i) ∈ (G.source e).map G.vertexLabel :=
    List.mem_map_of_mem source
  change I[i] ∈ (G.source e).map (Port.label G.internalLabel) at mem
  rw [G.source_typed,label,primitive_input] at mem
  change I[i] ∈ primitiveSignature.input p at mem
  rw [typed] at mem
  exact primitive_input_not_thunk p nonhole n mem

variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
include cert

/-- Every actual right primitive sourced at an original host vertex has a
retained original owner; the new outside contraction cannot be selected there. -/
theorem right_primitive_retained {v : C.Vertex} {e : (C.expand R).Edge} {p : Primitive}
    (source : Net.Expansion.host C R v ∈ (C.expand R).source e)
    (label : (C.expand R).edgeLabel e = primitiveLabel d p) (nonhole : ∀ h, p ≠ .hole h) :
    Nonempty (Retained C R e.1) := by
  rcases (cert e.1).origin with copies | ⟨h,_,pair⟩
  · exact copies.2
  · obtain ⟨i,mem⟩ := source_input C source
    obtain ⟨n,typed⟩ := pair.inputs_thunk i
    exact False.elim (primitive_no_thunk_source (R e.1) e.2 p label nonhole i n typed mem)

/-- A shallow original hole cannot own such a primitive even if an unfilled
hole corolla had been permitted by the structural certificate. -/
theorem right_primitive_not_hole (closed : HoleFree (C.expand R))
    {v : C.Vertex} {e : (C.expand R).Edge} {p : Primitive}
    (source : Net.Expansion.host C R v ∈ (C.expand R).source e)
    (label : (C.expand R).edgeLabel e = primitiveLabel d p) (nonhole : ∀ h, p ≠ .hole h) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h hole
  have pair := (cert e.1).converse.relation_at_hole hole closed
  obtain ⟨i,mem⟩ := source_input C source
  obtain ⟨n,typed⟩ := pair.inputs_thunk i
  exact primitive_no_thunk_source (R e.1) e.2 p label nonhole i n typed mem

/-- Every primitive on an actual selected local ancestry remains outside
shallow BPullC holes. In particular this applies to minimal term/atom spines;
no property of irrelevant sharing-tree siblings is assumed. -/
theorem right_primitive_ancestor_not_hole (closed : HoleFree (C.expand R))
    {J K} {A : Hypernet d J K} (f : MatchEmbedding A (C.expand R))
    (full : ∀ e, ∃ p, A.edgeLabel e = primitiveLabel d p ∧ ∀ h, p ≠ .hole h)
    {v : C.Vertex} {a b : A.Edge}
    (source : Net.Expansion.host C R v ∈ (C.expand R).source (f.edges a))
    (path : Ancestor A a b) :
    ∀ h, C.edgeLabel (f.edges b).1 ≠ primitiveLabel d (.hole h) := by
  induction path generalizing v with
  | refl =>
    obtain ⟨p,label,nonhole⟩ := full _
    exact right_primitive_not_hole C cert closed source (f.primitive _ _ label) nonhole
  | @step a b c adj path ih =>
    obtain ⟨p,label,nonhole⟩ := full a
    obtain ⟨copy⟩ := right_primitive_retained C cert source (f.primitive _ _ label) nonhole
    obtain ⟨w,target,next⟩ := f.adjacent adj
    obtain ⟨u,eq⟩ := copy.target_origin target
    exact ih (eq ▸ next)

/-- Hole freedom of the actual endpoint supplies the nonhole premise for
every primitive in a selected complete local footprint. -/
theorem right_primitive_footprint (closed : HoleFree (C.expand R))
    {J K} {A : Hypernet d J K} (f : MatchEmbedding A (C.expand R))
    (primitive : BoxPermutation.PrimitiveFootprint A) :
    ∀ e, ∃ p, A.edgeLabel e = primitiveLabel d p ∧ ∀ h, p ≠ .hole h := by
  intro e
  obtain ⟨p,label⟩ := primitive e
  refine ⟨p,label,?_⟩
  intro h eq
  subst p
  have holefree := closed (f.edges e)
  change LabelAll (fun p => ∀ h, p ≠ .hole h) d ((C.expand R).edgeLabel (f.edges e)) at holefree
  rw [f.primitive e _ label] at holefree
  cases d <;> exact holefree h rfl

/-- Primitive local-rule ancestries need no independently supplied nohole
certificate: it follows from the actual closed machine state. -/
theorem right_primitive_ancestry (closed : HoleFree (C.expand R))
    {J K} {A : Hypernet d J K} (f : MatchEmbedding A (C.expand R))
    (primitive : BoxPermutation.PrimitiveFootprint A)
    {v : C.Vertex} {a b : A.Edge}
    (source : Net.Expansion.host C R v ∈ (C.expand R).source (f.edges a))
    (path : Ancestor A a b) : ∀ h, C.edgeLabel (f.edges b).1 ≠ primitiveLabel d (.hole h) :=
  right_primitive_ancestor_not_hole C cert closed f (right_primitive_footprint C cert closed f primitive) source path

end Hypernets.Copying.BoxPullContraction
