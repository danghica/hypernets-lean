import Hypernets.Graph.Finite

/-!
Concrete finite interfaced labelled monoidal hypergraphs (§3.1).
Boundary vertices are distinguished constructors, in their prescribed order.
Only internal vertices and edges carry arbitrary names.
-/

namespace Hypernets.Graph

universe u

structure Signature (Label : Type) (Operation : Type u) where
  input : Operation → List Label
  output : Operation → List Label

inductive Port (Internal : Type) (inputs outputs : Nat) where
  | internal : Internal → Port Internal inputs outputs
  | input : Fin inputs → Port Internal inputs outputs
  | output : Fin outputs → Port Internal inputs outputs
  deriving DecidableEq

namespace Port

variable {V W : Type} {n m : Nat}

def IsInput : Port V n m → Prop
  | .input _ => True
  | _ => False

def IsOutput : Port V n m → Prop
  | .output _ => True
  | _ => False

def map (f : V → W) : Port V n m → Port W n m
  | .internal v => .internal (f v)
  | .input i => .input i
  | .output i => .output i

theorem map_injective {f : V → W} (inj : ∀ a b, f a = f b → a = b)
    {a b : Port V n m} (h : map f a = map f b) : a = b := by
  cases a <;> cases b <;> simp_all [map]
  exact inj _ _ h

@[simp] theorem map_isInput (f : V → W) (v : Port V n m) :
    (map f v).IsInput ↔ v.IsInput := by cases v <;> rfl

@[simp] theorem map_isOutput (f : V → W) (v : Port V n m) :
    (map f v).IsOutput ↔ v.IsOutput := by cases v <;> rfl

def label {L : Type} {I O : List L} (f : V → L) : Port V I.length O.length → L
  | .internal v => f v
  | .input i => I[i]
  | .output i => O[i]

end Port

/-- The paper's four incidence conditions, with a fixed operation signature.
The coverage equivalences say that the displayed inputs/outputs are all and
only boundary vertices; in particular there are no isolated vertices. -/
structure Net {L : Type} {Op : Type u} (σ : Signature L Op) (I O : List L) where
  Internal : Type
  Edge : Type
  finiteInternal : Enumeration Internal
  finiteEdge : Enumeration Edge
  internalLabel : Internal → L
  edgeLabel : Edge → Op
  source : Edge → List (Port Internal I.length O.length)
  target : Edge → List (Port Internal I.length O.length)
  source_nodup : ∀ e, (source e).Nodup
  target_nodup : ∀ e, (target e).Nodup
  source_unique : ∀ {v e f}, v ∈ source e → v ∈ source f → e = f
  target_unique : ∀ {v e f}, v ∈ target e → v ∈ target f → e = f
  source_coverage : ∀ v, (∃ e, v ∈ source e) ↔ ¬ v.IsOutput
  target_coverage : ∀ v, (∃ e, v ∈ target e) ↔ ¬ v.IsInput
  source_typed : ∀ e, (source e).map (Port.label internalLabel) = σ.input (edgeLabel e)
  target_typed : ∀ e, (target e).map (Port.label internalLabel) = σ.output (edgeLabel e)

namespace Net

variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (G : Net σ I O)

abbrev Vertex := Port G.Internal I.length O.length

def vertexLabel : G.Vertex → L := Port.label G.internalLabel

theorem source_not_output {e : G.Edge} {v : G.Vertex} (h : v ∈ G.source e) :
    ¬ v.IsOutput := (G.source_coverage v).mp ⟨e, h⟩

theorem target_not_input {e : G.Edge} {v : G.Vertex} (h : v ∈ G.target e) :
    ¬ v.IsInput := (G.target_coverage v).mp ⟨e, h⟩

theorem source_length (e : G.Edge) : (G.source e).length = (σ.input (G.edgeLabel e)).length := by
  have := congrArg List.length (G.source_typed e)
  simpa using this

theorem target_length (e : G.Edge) : (G.target e).length = (σ.output (G.edgeLabel e)).length := by
  have := congrArg List.length (G.target_typed e)
  simpa using this

def sourcePort (e : G.Edge) (i : Fin (σ.input (G.edgeLabel e)).length) : G.Vertex :=
  (G.source e)[i.val]'(by rw [G.source_length]; exact i.isLt)

def targetPort (e : G.Edge) (i : Fin (σ.output (G.edgeLabel e)).length) : G.Vertex :=
  (G.target e)[i.val]'(by rw [G.target_length]; exact i.isLt)

theorem sourcePort_mem (e : G.Edge) (i) : G.sourcePort e i ∈ G.source e := List.getElem_mem ..

theorem targetPort_mem (e : G.Edge) (i) : G.targetPort e i ∈ G.target e := List.getElem_mem ..

theorem sourcePort_injective (e : G.Edge) {i j} (h : G.sourcePort e i = G.sourcePort e j) : i = j := by
  apply Fin.ext
  exact (G.source_nodup e).eq_of_getElem_eq _ _ h

theorem targetPort_injective (e : G.Edge) {i j} (h : G.targetPort e i = G.targetPort e j) : i = j := by
  apply Fin.ext
  exact (G.target_nodup e).eq_of_getElem_eq _ _ h

theorem sourcePort_label (e : G.Edge) (i) :
    G.vertexLabel (G.sourcePort e i) = (σ.input (G.edgeLabel e))[i] := by
  have h := congrArg (fun xs => xs[i.val]?) (G.source_typed e)
  simpa [List.getElem?_eq_getElem, sourcePort, vertexLabel, G.source_length, i.isLt] using h

theorem targetPort_label (e : G.Edge) (i) :
    G.vertexLabel (G.targetPort e i) = (σ.output (G.edgeLabel e))[i] := by
  have h := congrArg (fun xs => xs[i.val]?) (G.target_typed e)
  simpa [List.getElem?_eq_getElem, targetPort, vertexLabel, G.target_length, i.isLt] using h

theorem mem_source_iff_port (e : G.Edge) (v : G.Vertex) :
    v ∈ G.source e ↔ ∃ i, G.sourcePort e i = v := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨i, by rw [← G.source_length]; exact hi.1⟩, hi.2⟩
  · rintro ⟨i, rfl⟩
    exact G.sourcePort_mem e i

theorem mem_target_iff_port (e : G.Edge) (v : G.Vertex) :
    v ∈ G.target e ↔ ∃ i, G.targetPort e i = v := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨i, by rw [← G.target_length]; exact hi.1⟩, hi.2⟩
  · rintro ⟨i, rfl⟩
    exact G.targetPort_mem e i

end Net
end Hypernets.Graph
