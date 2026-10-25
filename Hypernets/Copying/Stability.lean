import Hypernets.Copying.Predicates
import Hypernets.Graph.FiniteTrace

/-! Definition 10.3, specialised to the full example operation alphabet.
Stability is flat: boxes are attached beyond its thunk outputs, not admitted
as stable edges. Reachability and the output condition remain explicit. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- The primitive labels permitted in a stable graph. -/
def StablePrimitive : Primitive → Prop
  | .instanceEdge => True
  | .operation o => o.kind = .passive
  | _ => False

/-- Stable labels are primitive instances or passive operations, never boxes. -/
def StableLabel (d : Nat) (label : (alphabet d).Symbol) : Prop :=
  ∃ p, label = primitiveLabel d p ∧ StablePrimitive p

/-- The permitted external outputs in Definition 10.3. -/
def StableOutput : Wire → Prop
  | .atom | .thunk _ => True
  | .term => False

/-- Vertex reachability follows directed source-to-target incidences. -/
def VertexStep {d I O} (G : Hypernet d I O) (v w : G.Vertex) : Prop :=
  ∃ e, v ∈ G.source e ∧ w ∈ G.target e

def VertexReach {d I O} (G : Hypernet d I O) (v w : G.Vertex) : Prop :=
  ∃ n, Trace (VertexStep G) v w n

/-- The paper's stability conditions, including all-vertex input reachability. -/
structure Stable {d O} (G : Hypernet d [.term] O) : Prop where
  labels : ∀ e, StableLabel d (G.edgeLabel e)
  outputs : ∀ i : Fin O.length, StableOutput O[i]
  reachable : ∀ v, VertexReach G (.input 0) v

namespace Stable

theorem primitive_input {p : Primitive} (h : StablePrimitive p) :
    primitiveSignature.input p = [.term] := by
  cases p <;> simp_all [StablePrimitive, primitiveSignature]

theorem primitive_outputs {p : Primitive} (h : StablePrimitive p) :
    ∀ w ∈ primitiveSignature.output p, StableOutput w := by
  cases p with
  | instanceEdge => simp [primitiveSignature, StableOutput]
  | operation o => cases o <;> simp_all [StablePrimitive, Operation.kind, primitiveSignature, Operation.outputs, StableOutput]
  | _ => simp [StablePrimitive] at h

theorem source_type {d O} {G : Hypernet d [.term] O} (labels : ∀ e, StableLabel d (G.edgeLabel e))
    {e : G.Edge} {v : G.Vertex} (h : v ∈ G.source e) : G.vertexLabel v = .term := by
  obtain ⟨p,hp,stable⟩ := labels e
  have mem := List.mem_map_of_mem (f := G.vertexLabel) h
  dsimp only [Net.vertexLabel] at mem
  rw [G.source_typed, hp, Copying.primitive_input, primitive_input stable] at mem
  exact List.mem_singleton.mp mem

theorem target_type {d O} {G : Hypernet d [.term] O} (labels : ∀ e, StableLabel d (G.edgeLabel e))
    {e : G.Edge} {v : G.Vertex} (h : v ∈ G.target e) : StableOutput (G.vertexLabel v) := by
  obtain ⟨p,hp,stable⟩ := labels e
  have mem := List.mem_map_of_mem (f := G.vertexLabel) h
  dsimp only [Net.vertexLabel] at mem
  rw [G.target_typed, hp, Copying.primitive_output] at mem
  exact primitive_outputs stable _ mem

/-- In this alphabet, an internal vertex would need to be both term and non-term. -/
theorem no_internal {d O} {G : Hypernet d [.term] O} (labels : ∀ e, StableLabel d (G.edgeLabel e))
    (v : G.Internal) : False := by
  obtain ⟨e,he⟩ := (G.source_coverage (.internal v)).mpr (by simp [Port.IsOutput])
  obtain ⟨f,hf⟩ := (G.target_coverage (.internal v)).mpr (by simp [Port.IsInput])
  have ht := target_type labels hf
  rw [source_type labels he] at ht
  exact ht

/-- Every permitted edge consumes the unique external input. -/
theorem input_source {d O} {G : Hypernet d [.term] O} (labels : ∀ e, StableLabel d (G.edgeLabel e))
    (e : G.Edge) : Port.input 0 ∈ G.source e := by
  obtain ⟨p,hp,stable⟩ := labels e
  have len : (G.source e).length = 1 := by
    rw [G.source_length, hp, Copying.primitive_input, primitive_input stable]; rfl
  cases hs : G.source e with
  | nil => simp [hs] at len
  | cons v vs =>
    have mem : v ∈ G.source e := by simp [hs]
    cases v with
    | internal v => exact False.elim (no_internal labels v)
    | output i => exact False.elim (G.source_not_output mem trivial)
    | input i =>
      have eq : i = 0 := Fin.ext (by change i.val = 0; have := i.isLt; change i.val < 1 at this; omega)
      simp [eq]

/-- All stable edges coincide; this is specific to the example passive signatures. -/
theorem edge_unique {d O} {G : Hypernet d [.term] O} (h : Stable G) (e f : G.Edge) : e = f :=
  G.source_unique (input_source h.labels e) (input_source h.labels f)

/-- The sole input guarantees an edge exists; together with uniqueness this
rules out vacuous empty stable graphs. -/
theorem exists_unique_edge {d O} {G : Hypernet d [.term] O} (h : Stable G) :
    ∃ e : G.Edge, ∀ f : G.Edge, f = e := by
  obtain ⟨e,_⟩ := (G.source_coverage (.input 0)).mpr (by simp [Port.IsOutput])
  exact ⟨e,fun f => edge_unique h f e⟩

/-- The output and reachability clauses are derivable for this specific alphabet. -/
theorem of_labels {d O} {G : Hypernet d [.term] O} (labels : ∀ e, StableLabel d (G.edgeLabel e)) : Stable G where
  labels := labels
  outputs i := by
    obtain ⟨e,he⟩ := (G.target_coverage (.output i)).mpr (by simp [Port.IsInput])
    exact target_type labels he
  reachable v := by
    cases v with
    | internal v => exact False.elim (no_internal labels v)
    | input i =>
      have eq : i = 0 := Fin.ext (by change i.val = 0; have := i.isLt; change i.val < 1 at this; omega)
      subst i
      exact ⟨0,.refl _⟩
    | output i =>
      obtain ⟨e,he⟩ := (G.target_coverage (.output i)).mpr (by simp [Port.IsInput])
      exact ⟨1,.step ⟨e,input_source labels e,he⟩ (.refl _)⟩

/-- Stability forbids a directed adjacency between two outer edges. -/
theorem no_adjacency {d O} {G : Hypernet d [.term] O} (h : Stable G) (e f : G.Edge) : ¬ G.Adjacent e f := by
  rintro ⟨v,ht,hs⟩
  have out := target_type h.labels ht
  rw [source_type h.labels hs] at out
  exact out

/-- Constants satisfy the complete stability predicate at every allowance. -/
theorem constant (d : Nat) (c : Constant) : Stable (primitiveNet d (.operation (.const c))) :=
  by
  apply of_labels
  intro e
  refine ⟨.operation (.const c),?_,rfl⟩
  cases d <;> rfl

theorem lambda (d : Nat) : Stable (primitiveNet d (.operation .lam)) :=
  by
  apply of_labels
  intro e
  refine ⟨.operation .lam,?_,rfl⟩
  cases d <;> rfl

theorem instanceEdge (d : Nat) : Stable (primitiveNet d .instanceEdge) :=
  by
  apply of_labels
  intro e
  refine ⟨.instanceEdge,?_,trivial⟩
  cases d <;> rfl

theorem focusFree {d O} {G : Hypernet d [.term] O} (h : Stable G) : FocusFree G := by
  intro e
  obtain ⟨p,eq,stable⟩ := h.labels e
  rw [eq]
  cases d <;> change ∀ m, p ≠ .focus m
  all_goals intro m eq; subst p; exact stable

theorem holeFree {d O} {G : Hypernet d [.term] O} (h : Stable G) : HoleFree G := by
  intro e
  obtain ⟨p,eq,stable⟩ := h.labels e
  rw [eq]
  cases d <;> change ∀ m, p ≠ .hole m
  all_goals intro m eq; subst p; exact stable

/-- Recursive renaming preserves the flat primitive restriction. -/
theorem label_equiv (d : Nat) {a b : (alphabet d).Symbol} (h : LabelEquiv d a b) :
    StableLabel d a ↔ StableLabel d b := by
  cases d with
  | zero => change a = b at h; cases h; rfl
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => change a = b at h; cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => simp [StableLabel, primitiveLabel]

theorem iso {d O} {G H : Hypernet d [.term] O} (f : DeepIso G H) (h : Stable G) : Stable H := by
  apply of_labels
  intro e
  have ht := (label_equiv d (f.edge_label (f.edges.invFun e))).mp (h.labels _)
  simpa [f.edges.right_inv] using ht

theorem iso_iff {d O} {G H : Hypernet d [.term] O} (f : DeepIso G H) : Stable G ↔ Stable H :=
  ⟨iso f,iso f.symm⟩

end Stable
end Hypernets.Copying
