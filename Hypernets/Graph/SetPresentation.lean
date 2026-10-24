import Hypernets.Graph.Hierarchy
import Hypernets.Graph.RelIso

/-! Arbitrary finite vertex sets with ordered boundary embeddings, as in §3.1.
The conversion to `Net` is a change of vertex names, not a restriction on incidence. -/
namespace Hypernets.Graph
universe u

/-- A signature-typed set presentation. Boundary functions enumerate exactly
those vertices missing a target/source incidence; the two boundaries are disjoint. -/
structure SetNet {L : Type} {Op : Type u} (σ : Signature L Op) (I O : List L) where
  Vertex : Type
  Edge : Type
  finiteVertex : Enumeration Vertex
  finiteEdge : Enumeration Edge
  vertexLabel : Vertex → L
  edgeLabel : Edge → Op
  input : Fin I.length → Vertex
  output : Fin O.length → Vertex
  input_injective : ∀ {i j}, input i = input j → i = j
  output_injective : ∀ {i j}, output i = output j → i = j
  disjoint : ∀ i j, input i ≠ output j
  input_label : ∀ i, vertexLabel (input i) = I[i]
  output_label : ∀ i, vertexLabel (output i) = O[i]
  source : Edge → List Vertex
  target : Edge → List Vertex
  source_nodup : ∀ e, (source e).Nodup
  target_nodup : ∀ e, (target e).Nodup
  source_unique : ∀ {v e f}, v ∈ source e → v ∈ source f → e = f
  target_unique : ∀ {v e f}, v ∈ target e → v ∈ target f → e = f
  source_coverage : ∀ v, (∃ e, v ∈ source e) ↔ ¬ ∃ j, output j = v
  target_coverage : ∀ v, (∃ e, v ∈ target e) ↔ ¬ ∃ i, input i = v
  source_typed : ∀ e, (source e).map vertexLabel = σ.input (edgeLabel e)
  target_typed : ∀ e, (target e).map vertexLabel = σ.output (edgeLabel e)

namespace SetNet
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- Interior vertices are precisely those absent from both boundary lists. -/
def Interior (G : SetNet σ I O) :=
  {v : G.Vertex // (¬ ∃ i, G.input i = v) ∧ (¬ ∃ j, G.output j = v)}

/-- Forget the tags on a normalized vertex. -/
def decode (G : SetNet σ I O) : Port G.Interior I.length O.length → G.Vertex
  | .internal v => v.val
  | .input i => G.input i
  | .output j => G.output j

/-- Classify a vertex as input, output, or interior, retaining its boundary index. -/
noncomputable def encode (G : SetNet σ I O) (v : G.Vertex) : Port G.Interior I.length O.length := by
  classical
  exact if h : ∃ i, G.input i = v then .input (Classical.choose h)
    else if k : ∃ j, G.output j = v then .output (Classical.choose k)
    else .internal ⟨v,h,k⟩

theorem decode_encode (G : SetNet σ I O) (v : G.Vertex) : G.decode (G.encode v) = v := by
  classical
  unfold encode
  split
  next h => exact Classical.choose_spec h
  next h => split
            next k => exact Classical.choose_spec k
            next k => rfl

theorem decode_injective (G : SetNet σ I O) {v w} (eq : G.decode v = G.decode w) : v = w := by
  cases v with
  | internal v => cases w with
    | internal w => exact congrArg Port.internal (Subtype.ext eq)
    | input i => exact False.elim (v.property.1 ⟨i,eq.symm⟩)
    | output j => exact False.elim (v.property.2 ⟨j,eq.symm⟩)
  | input i => cases w with
    | internal w => exact False.elim (w.property.1 ⟨i,eq⟩)
    | input j => exact congrArg Port.input (G.input_injective eq)
    | output j => exact False.elim (G.disjoint i j eq)
  | output i => cases w with
    | internal w => exact False.elim (w.property.2 ⟨i,eq⟩)
    | input j => exact False.elim (G.disjoint j i eq.symm)
    | output j => exact congrArg Port.output (G.output_injective eq)

theorem encode_decode (G : SetNet σ I O) (v) : G.encode (G.decode v) = v :=
  G.decode_injective (G.decode_encode _)

/-- The explicit bijection between arbitrary vertices and tagged vertices. -/
noncomputable def vertices (G : SetNet σ I O) : Bijection G.Vertex (Port G.Interior I.length O.length) :=
  ⟨G.encode,G.decode,G.decode_encode,G.encode_decode⟩

theorem encode_label (G : SetNet σ I O) (v) :
    Port.label (fun x : G.Interior => G.vertexLabel x.val) (G.encode v) = G.vertexLabel v := by
  have all (p : Port G.Interior I.length O.length) :
      Port.label (fun x : G.Interior => G.vertexLabel x.val) p = G.vertexLabel (G.decode p) := by
    cases p with
    | internal x => rfl
    | input i => exact (G.input_label i).symm
    | output j => exact (G.output_label j).symm
  rw [all,G.decode_encode]

theorem output_iff (G : SetNet σ I O) (v) :
    (G.encode v).IsOutput ↔ ∃ j, G.output j = v := by
  constructor
  · intro h
    have eq := G.decode_encode v
    cases p : G.encode v with
    | internal x => rw [p] at h; exact False.elim h
    | input i => rw [p] at h; exact False.elim h
    | output j => exact ⟨j,by simpa [p,decode] using eq⟩
  · rintro ⟨j,rfl⟩
    have eq := G.encode_decode (.output j)
    change G.encode (G.output j) = .output j at eq
    rw [eq]; trivial

theorem input_iff (G : SetNet σ I O) (v) :
    (G.encode v).IsInput ↔ ∃ i, G.input i = v := by
  constructor
  · intro h
    have eq := G.decode_encode v
    cases p : G.encode v with
    | internal x => rw [p] at h; exact False.elim h
    | output j => rw [p] at h; exact False.elim h
    | input i => exact ⟨i,by simpa [p,decode] using eq⟩
  · rintro ⟨i,rfl⟩
    have eq := G.encode_decode (.input i)
    change G.encode (G.input i) = .input i at eq
    rw [eq]; trivial

/-- Normalize the boundary representation, preserving edges and ordered incidence. -/
noncomputable def toNet (G : SetNet σ I O) : Net σ I O where
  Internal := G.Interior
  Edge := G.Edge
  finiteInternal := G.finiteVertex.subtype _
  finiteEdge := G.finiteEdge
  internalLabel v := G.vertexLabel v.val
  edgeLabel := G.edgeLabel
  source e := (G.source e).map G.encode
  target e := (G.target e).map G.encode
  source_nodup e := nodup_map_on (G.source_nodup e) (fun _ _ _ _ eq => G.vertices.injective eq)
  target_nodup e := nodup_map_on (G.target_nodup e) (fun _ _ _ _ eq => G.vertices.injective eq)
  source_unique := by
    intro v e f he hf
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp he
    obtain ⟨b,hb,eq'⟩ := List.mem_map.mp hf
    have ab := G.vertices.injective (eq.trans eq'.symm)
    exact G.source_unique ha (ab ▸ hb)
  target_unique := by
    intro v e f he hf
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp he
    obtain ⟨b,hb,eq'⟩ := List.mem_map.mp hf
    have ab := G.vertices.injective (eq.trans eq'.symm)
    exact G.target_unique ha (ab ▸ hb)
  source_coverage := by
    intro v
    have mem (e) : v ∈ (G.source e).map G.encode ↔ G.decode v ∈ G.source e := by
      constructor
      · rintro h; obtain ⟨a,ha,eq⟩ := List.mem_map.mp h
        have same := congrArg G.decode eq
        rw [G.decode_encode] at same
        exact same ▸ ha
      · intro h; exact List.mem_map.mpr ⟨_,h,G.encode_decode v⟩
    simp only [mem]
    rw [G.source_coverage,← G.output_iff,G.encode_decode]
  target_coverage := by
    intro v
    have mem (e) : v ∈ (G.target e).map G.encode ↔ G.decode v ∈ G.target e := by
      constructor
      · rintro h; obtain ⟨a,ha,eq⟩ := List.mem_map.mp h
        have same := congrArg G.decode eq
        rw [G.decode_encode] at same
        exact same ▸ ha
      · intro h; exact List.mem_map.mpr ⟨_,h,G.encode_decode v⟩
    simp only [mem]
    rw [G.target_coverage,← G.input_iff,G.encode_decode]
  source_typed e := by simpa only [List.map_map,Function.comp_def,G.encode_label] using G.source_typed e
  target_typed e := by simpa only [List.map_map,Function.comp_def,G.encode_label] using G.target_typed e

/-- Isomorphism of set presentations fixes the order of each boundary. -/
structure Iso (G H : SetNet σ I O) where
  vertices : Bijection G.Vertex H.Vertex
  edges : Bijection G.Edge H.Edge
  vertex_label : ∀ v, H.vertexLabel (vertices.toFun v) = G.vertexLabel v
  edge_label : ∀ e, H.edgeLabel (edges.toFun e) = G.edgeLabel e
  input : ∀ i, vertices.toFun (G.input i) = H.input i
  output : ∀ j, vertices.toFun (G.output j) = H.output j
  source : ∀ e, (G.source e).map vertices.toFun = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map vertices.toFun = H.target (edges.toFun e)
end SetNet

namespace Net
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- Expose every vertex as an ordinary element of one finite carrier. -/
def toSet (G : Net σ I O) : SetNet σ I O where
  Vertex := G.Vertex
  Edge := G.Edge
  finiteVertex := {
    elements := G.finiteInternal.elements.map Port.internal ++
      (List.finRange I.length).map Port.input ++ (List.finRange O.length).map Port.output
    complete := by
      intro v
      cases v with
      | internal x => simp only [List.mem_append]; exact .inl (.inl (List.mem_map_of_mem (G.finiteInternal.complete x)))
      | input i => simp only [List.mem_append]; exact .inl (.inr (List.mem_map_of_mem (List.mem_finRange i)))
      | output j => simp only [List.mem_append]; exact .inr (List.mem_map_of_mem (List.mem_finRange j))
  }
  finiteEdge := G.finiteEdge
  vertexLabel := G.vertexLabel
  edgeLabel := G.edgeLabel
  input := Port.input
  output := Port.output
  input_injective := fun h => Port.input.inj h
  output_injective := fun h => Port.output.inj h
  disjoint := by intro i j h; cases h
  input_label _ := rfl
  output_label _ := rfl
  source := G.source
  target := G.target
  source_nodup := G.source_nodup
  target_nodup := G.target_nodup
  source_unique := G.source_unique
  target_unique := G.target_unique
  source_coverage := by intro v; rw [G.source_coverage]; cases v <;> simp [Port.IsOutput]
  target_coverage := by intro v; rw [G.target_coverage]; cases v <;> simp [Port.IsInput]
  source_typed := G.source_typed
  target_typed := G.target_typed
/-- Every set presentation is recovered up to a boundary-preserving isomorphism. -/
noncomputable def set_roundtrip (G : SetNet σ I O) : SetNet.Iso G G.toNet.toSet where
  vertices := G.vertices
  edges := Bijection.refl _
  vertex_label := G.encode_label
  edge_label _ := rfl
  input i := G.encode_decode (.input i)
  output j := G.encode_decode (.output j)
  source _ := rfl
  target _ := rfl

/-- The interior of an exposed tagged graph contains exactly its old internal vertices. -/
def interiorBijection (G : Net σ I O) : Bijection G.Internal G.toSet.Interior where
  toFun v := ⟨.internal v,⟨(by rintro ⟨i,h⟩; cases h),(by rintro ⟨j,h⟩; cases h)⟩⟩
  invFun v := match v with
    | ⟨.internal x,_⟩ => x
    | ⟨.input i,h,_⟩ => False.elim (h ⟨i,rfl⟩)
    | ⟨.output j,_,h⟩ => False.elim (h ⟨j,rfl⟩)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v,h,k⟩
    cases v with
    | internal v => rfl
    | input i => exact False.elim (h ⟨i,rfl⟩)
    | output j => exact False.elim (k ⟨j,rfl⟩)

theorem encode_toSet (G : Net σ I O) (v : G.Vertex) :
    G.toSet.encode v = Port.map G.interiorBijection.toFun v := by
  apply G.toSet.decode_injective
  exact (G.toSet.decode_encode v).trans (by cases v <;> rfl)

/-- Conversely, normalization recovers an existing `Net` up to its ordinary isomorphism. -/
noncomputable def roundtrip (G : Net σ I O) : Iso G G.toSet.toNet where
  vertices := G.interiorBijection
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := rfl
  source e := by
    change (G.source e).map (Port.map G.interiorBijection.toFun) = (G.source e).map G.toSet.encode
    exact List.map_congr_left (fun v _ => (G.encode_toSet v).symm)
  target e := by
    change (G.target e).map (Port.map G.interiorBijection.toFun) = (G.target e).map G.toSet.encode
    exact List.map_congr_left (fun v _ => (G.encode_toSet v).symm)
end Net
end Hypernets.Graph

namespace Hypernets.Graph.SetNet
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
/-- A set-graph isomorphism whose labels are compared recursively. -/
structure RelIso (R : Op → Op → Prop) (G H : SetNet σ I O) where
  vertices : Bijection G.Vertex H.Vertex
  edges : Bijection G.Edge H.Edge
  vertex_label : ∀ v, H.vertexLabel (vertices.toFun v) = G.vertexLabel v
  edge_label : ∀ e, R (G.edgeLabel e) (H.edgeLabel (edges.toFun e))
  input : ∀ i, vertices.toFun (G.input i) = H.input i
  output : ∀ j, vertices.toFun (G.output j) = H.output j
  source : ∀ e, (G.source e).map vertices.toFun = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map vertices.toFun = H.target (edges.toFun e)

/-- Relabelling a set graph changes no vertex, incidence or boundary data. -/
@[reducible] def relabel {Op' : Type u} (G : SetNet σ I O) (τ : Signature L Op')
    (f : Op → Op') (hi : ∀ a, τ.input (f a) = σ.input a)
    (ho : ∀ a, τ.output (f a) = σ.output a) : SetNet τ I O where
  Vertex := G.Vertex
  Edge := G.Edge
  finiteVertex := G.finiteVertex
  finiteEdge := G.finiteEdge
  vertexLabel := G.vertexLabel
  edgeLabel e := f (G.edgeLabel e)
  input := G.input
  output := G.output
  input_injective := G.input_injective
  output_injective := G.output_injective
  disjoint := G.disjoint
  input_label := G.input_label
  output_label := G.output_label
  source := G.source
  target := G.target
  source_nodup := G.source_nodup
  target_nodup := G.target_nodup
  source_unique := G.source_unique
  target_unique := G.target_unique
  source_coverage := G.source_coverage
  target_coverage := G.target_coverage
  source_typed e := (G.source_typed e).trans (hi _).symm
  target_typed e := (G.target_typed e).trans (ho _).symm
end Hypernets.Graph.SetNet

namespace Hypernets.Graph.SetNet.RelIso
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R : Op → Op → Prop} {G H : SetNet σ I O}

/-- Boundary membership is preserved and reflected by a set-graph isomorphism. -/
theorem input_iff (f : RelIso R G H) (v : G.Vertex) :
    (∃ i, H.input i = f.vertices.toFun v) ↔ ∃ i, G.input i = v := by
  constructor
  · rintro ⟨i,h⟩; exact ⟨i,f.vertices.injective ((f.input i).trans h)⟩
  · rintro ⟨i,rfl⟩; exact ⟨i,(f.input i).symm⟩

theorem output_iff (f : RelIso R G H) (v : G.Vertex) :
    (∃ i, H.output i = f.vertices.toFun v) ↔ ∃ i, G.output i = v := by
  constructor
  · rintro ⟨i,h⟩; exact ⟨i,f.vertices.injective ((f.output i).trans h)⟩
  · rintro ⟨i,rfl⟩; exact ⟨i,(f.output i).symm⟩

/-- Restrict the vertex bijection to vertices belonging to neither boundary. -/
def interiors (f : RelIso R G H) : Bijection G.Interior H.Interior where
  toFun v := ⟨f.vertices.toFun v.val,
    (fun h => v.property.1 ((f.input_iff v.val).mp h)),
    (fun h => v.property.2 ((f.output_iff v.val).mp h))⟩
  invFun v := ⟨f.vertices.invFun v.val,
    (fun h => v.property.1 (by obtain ⟨i,h⟩ := h; exact ⟨i,by rw [← f.input,h,f.vertices.right_inv]⟩)),
    (fun h => v.property.2 (by obtain ⟨i,h⟩ := h; exact ⟨i,by rw [← f.output,h,f.vertices.right_inv]⟩))⟩
  left_inv v := Subtype.ext (f.vertices.left_inv v.val)
  right_inv v := Subtype.ext (f.vertices.right_inv v.val)

theorem encode_map (f : RelIso R G H) (v : G.Vertex) :
    Port.map f.interiors.toFun (G.encode v) = H.encode (f.vertices.toFun v) := by
  apply H.decode_injective
  rw [H.decode_encode]
  have comm (p : Port G.Interior I.length O.length) :
      H.decode (Port.map f.interiors.toFun p) = f.vertices.toFun (G.decode p) := by
    cases p with
    | internal x => rfl
    | input i => exact (f.input i).symm
    | output j => exact (f.output j).symm
  rw [comm,G.decode_encode]

/-- Normalization transports all set-graph isomorphisms. -/
noncomputable def toNet (f : RelIso R G H) : Net.RelIso R G.toNet H.toNet where
  vertices := f.interiors
  edges := f.edges
  internal_label v := f.vertex_label v.val
  edge_label := f.edge_label
  source e := by
    change G.Edge at e
    change ((G.source e).map G.encode).map (Port.map f.interiors.toFun) =
      (H.source (f.edges.toFun e)).map H.encode
    rw [← f.source,List.map_map,List.map_map]
    exact List.map_congr_left (fun v _ => f.encode_map v)
  target e := by
    change G.Edge at e
    change ((G.target e).map G.encode).map (Port.map f.interiors.toFun) =
      (H.target (f.edges.toFun e)).map H.encode
    rw [← f.target,List.map_map,List.map_map]
    exact List.map_congr_left (fun v _ => f.encode_map v)
end Hypernets.Graph.SetNet.RelIso
