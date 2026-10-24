import Hypernets.Graph.SetPresentation

/-! Actual finite vertex-name sets. Prefixes are names, not graph labels. -/
namespace Hypernets.Graph
universe u

/-- A common ambient set of vertex names; all three coordinates are natural numbers. -/
abbrev VertexName := Nat × Nat × Nat

/-- A set graph whose vertices are literally members of a finite subset of the
common name space. Boundary vertices have ordinary names as well. -/
structure NamedNet {L : Type} {Op : Type u} (σ : Signature L Op) (I O : List L) where
  names : List VertexName
  Edge : Type
  finiteEdge : Enumeration Edge
  vertexLabel : {v : VertexName // v ∈ names} → L
  edgeLabel : Edge → Op
  input : Fin I.length → {v : VertexName // v ∈ names}
  output : Fin O.length → {v : VertexName // v ∈ names}
  input_injective : ∀ {i j}, input i = input j → i = j
  output_injective : ∀ {i j}, output i = output j → i = j
  disjoint : ∀ i j, input i ≠ output j
  input_label : ∀ i, vertexLabel (input i) = I[i]
  output_label : ∀ i, vertexLabel (output i) = O[i]
  source : Edge → List {v : VertexName // v ∈ names}
  target : Edge → List {v : VertexName // v ∈ names}
  source_nodup : ∀ e, (source e).Nodup
  target_nodup : ∀ e, (target e).Nodup
  source_unique : ∀ {v e f}, v ∈ source e → v ∈ source f → e = f
  target_unique : ∀ {v e f}, v ∈ target e → v ∈ target f → e = f
  source_coverage : ∀ v, (∃ e, v ∈ source e) ↔ ¬ ∃ j, output j = v
  target_coverage : ∀ v, (∃ e, v ∈ target e) ↔ ¬ ∃ i, input i = v
  source_typed : ∀ e, (source e).map vertexLabel = σ.input (edgeLabel e)
  target_typed : ∀ e, (target e).map vertexLabel = σ.output (edgeLabel e)

namespace NamedNet
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- Expose the named vertex subset as a set-graph carrier. Repetitions in the
finite enumeration do not duplicate vertices, which form a subtype. -/
@[reducible] def toSet (G : NamedNet σ I O) : SetNet σ I O where
  Vertex := {v : VertexName // v ∈ G.names}
  Edge := G.Edge
  finiteVertex := ⟨G.names.attach,by intro v; exact List.mem_attach _ v⟩
  finiteEdge := G.finiteEdge
  vertexLabel := G.vertexLabel
  edgeLabel := G.edgeLabel
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
  source_typed := G.source_typed
  target_typed := G.target_typed

/-- A canonical numerical identifier from an exhaustive enumeration. -/
noncomputable def index {V : Type} (finite : Enumeration V) (v : V) : Nat := by
  classical
  exact finite.elements.idxOf v

theorem index_injective {V : Type} (finite : Enumeration V) {v w : V}
    (eq : index finite v = index finite w) : v = w := by
  classical
  have h := congrArg (fun i => finite.elements[i]?) eq
  simpa [index,List.getElem?_eq_getElem,List.idxOf_lt_length_iff.mpr (finite.complete v),
    List.idxOf_lt_length_iff.mpr (finite.complete w)] using h

/-- Assign a common two-coordinate prefix and distinct numerical suffixes. -/
noncomputable def name {V : Type} (finite : Enumeration V) (a b : Nat) (v : V) : VertexName :=
  (a,b,index finite v)

noncomputable def freshNames (G : SetNet σ I O) (a b : Nat) : List VertexName :=
  G.finiteVertex.elements.map (name G.finiteVertex a b)

/-- The fresh named carrier is bijective to the old carrier, including boundaries. -/
noncomputable def naming (G : SetNet σ I O) (a b : Nat) :
    Bijection G.Vertex {v : VertexName // v ∈ freshNames G a b} := by
  classical
  have inj : ∀ {v w : G.Vertex}, name G.finiteVertex a b v = name G.finiteVertex a b w → v = w :=
    fun h => index_injective G.finiteVertex (congrArg (fun x : VertexName => x.2.2) h)
  have preimage (x : {v : VertexName // v ∈ freshNames G a b}) : ∃ v, name G.finiteVertex a b v = x.val := by
    obtain ⟨v,_,h⟩ := List.mem_map.mp x.property
    exact ⟨v,h⟩
  exact {
    toFun v := ⟨name G.finiteVertex a b v,List.mem_map_of_mem (G.finiteVertex.complete v)⟩
    invFun x := Classical.choose (preimage x)
    left_inv v := inj (Classical.choose_spec (preimage _))
    right_inv x := Subtype.ext (Classical.choose_spec (preimage x))
  }

/-- Freshening changes vertex names only. The edge carrier and all edge labels
are retained; source and target lists are mapped through the naming bijection. -/
noncomputable def ofSet (G : SetNet σ I O) (a b : Nat) : NamedNet σ I O where
  names := freshNames G a b
  Edge := G.Edge
  finiteEdge := G.finiteEdge
  vertexLabel v := G.vertexLabel ((naming G a b).invFun v)
  edgeLabel := G.edgeLabel
  input i := (naming G a b).toFun (G.input i)
  output j := (naming G a b).toFun (G.output j)
  input_injective h := G.input_injective ((naming G a b).injective h)
  output_injective h := G.output_injective ((naming G a b).injective h)
  disjoint i j h := G.disjoint i j ((naming G a b).injective h)
  input_label i := by rw [(naming G a b).left_inv]; exact G.input_label i
  output_label j := by rw [(naming G a b).left_inv]; exact G.output_label j
  source e := (G.source e).map (naming G a b).toFun
  target e := (G.target e).map (naming G a b).toFun
  source_nodup e := nodup_map_on (G.source_nodup e) (fun _ _ _ _ h => (naming G a b).injective h)
  target_nodup e := nodup_map_on (G.target_nodup e) (fun _ _ _ _ h => (naming G a b).injective h)
  source_unique := by
    intro v e f he hf
    obtain ⟨x,hx,eq⟩ := List.mem_map.mp he
    obtain ⟨y,hy,eq'⟩ := List.mem_map.mp hf
    exact G.source_unique hx ((naming G a b).injective (eq.trans eq'.symm) ▸ hy)
  target_unique := by
    intro v e f he hf
    obtain ⟨x,hx,eq⟩ := List.mem_map.mp he
    obtain ⟨y,hy,eq'⟩ := List.mem_map.mp hf
    exact G.target_unique hx ((naming G a b).injective (eq.trans eq'.symm) ▸ hy)
  source_coverage := by
    intro v
    have mem e : v ∈ (G.source e).map (naming G a b).toFun ↔ (naming G a b).invFun v ∈ G.source e := by
      constructor
      · rintro h; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
        simpa only [(naming G a b).left_inv] using hx
      · intro h; exact List.mem_map.mpr ⟨_,h,(naming G a b).right_inv v⟩
    simp only [mem,G.source_coverage]
    apply not_congr
    constructor
    · rintro ⟨i,h⟩; exact ⟨i,by rw [h,(naming G a b).right_inv]⟩
    · rintro ⟨i,h⟩
      exact ⟨i,((naming G a b).left_inv (G.output i)).symm.trans (congrArg (naming G a b).invFun h)⟩
  target_coverage := by
    intro v
    have mem e : v ∈ (G.target e).map (naming G a b).toFun ↔ (naming G a b).invFun v ∈ G.target e := by
      constructor
      · rintro h; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
        simpa only [(naming G a b).left_inv] using hx
      · intro h; exact List.mem_map.mpr ⟨_,h,(naming G a b).right_inv v⟩
    simp only [mem,G.target_coverage]
    apply not_congr
    constructor
    · rintro ⟨i,h⟩; exact ⟨i,by rw [h,(naming G a b).right_inv]⟩
    · rintro ⟨i,h⟩
      exact ⟨i,((naming G a b).left_inv (G.input i)).symm.trans (congrArg (naming G a b).invFun h)⟩
  source_typed e := by simpa only [List.map_map,Function.comp_def,(naming G a b).left_inv] using G.source_typed e
  target_typed e := by simpa only [List.map_map,Function.comp_def,(naming G a b).left_inv] using G.target_typed e

/-- Freshening is an ordinary label-preserving isomorphism. -/
noncomputable def ofSet_iso (G : SetNet σ I O) (a b : Nat) : SetNet.RelIso Eq G (ofSet G a b).toSet where
  vertices := naming G a b
  edges := Bijection.refl _
  vertex_label v := by exact congrArg G.vertexLabel ((naming G a b).left_inv v)
  edge_label _ := rfl
  input _ := rfl
  output _ := rfl
  source _ := rfl
  target _ := rfl

/-- The selected name prefix is visible at every input of the fresh graph. -/
theorem input_prefix (G : SetNet σ I O) (a b : Nat) (i : Fin I.length) :
    ((ofSet G a b).input i).val.1 = a ∧ ((ofSet G a b).input i).val.2.1 = b := ⟨rfl,rfl⟩
/-- Named freshening followed by boundary normalization changes only carriers. -/
noncomputable def typed_roundtrip (G : Net σ I O) (a b : Nat) :
    Net.Iso G (ofSet G.toSet a b).toSet.toNet := by
  let f := (ofSet_iso G.toSet a b).toNet
  exact (Net.roundtrip G).trans {
    vertices := f.vertices
    edges := f.edges
    internal_label := f.internal_label
    edge_label := fun e => (f.edge_label e).symm
    source := f.source
    target := f.target
  }
end NamedNet
end Hypernets.Graph

namespace Hypernets.Graph.SetNet
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op}

/-- Ordered-boundary isomorphism with possibly differently presented interface
indices. Boundary lists, not casts between finite index types, are compared. -/
structure HRelIso (R : Op → Op → Prop) {I O I' O'}
    (G : SetNet σ I O) (H : SetNet σ I' O') where
  vertices : Bijection G.Vertex H.Vertex
  edges : Bijection G.Edge H.Edge
  vertex_label : ∀ v, H.vertexLabel (vertices.toFun v) = G.vertexLabel v
  edge_label : ∀ e, R (G.edgeLabel e) (H.edgeLabel (edges.toFun e))
  input : (List.ofFn G.input).map vertices.toFun = List.ofFn H.input
  output : (List.ofFn G.output).map vertices.toFun = List.ofFn H.output
  source : ∀ e, (G.source e).map vertices.toFun = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map vertices.toFun = H.target (edges.toFun e)

namespace HRelIso
variable {R : Op → Op → Prop} {I O I' O' I'' O''}
    {G : SetNet σ I O} {H : SetNet σ I' O'} {K : SetNet σ I'' O''}

def ofRelIso {G H : SetNet σ I O} (f : RelIso R G H) : HRelIso R G H where
  vertices := f.vertices
  edges := f.edges
  vertex_label := f.vertex_label
  edge_label := f.edge_label
  input := by simp only [List.map_ofFn]; exact congrArg List.ofFn (funext f.input)
  output := by simp only [List.map_ofFn]; exact congrArg List.ofFn (funext f.output)
  source := f.source
  target := f.target

def ofIso {G H : SetNet σ I O} (f : Iso G H) : HRelIso Eq G H := ofRelIso {
  vertices := f.vertices
  edges := f.edges
  vertex_label := f.vertex_label
  edge_label := fun e => (f.edge_label e).symm
  input := f.input
  output := f.output
  source := f.source
  target := f.target
}

def trans (tr : ∀ {a b c}, R a b → R b c → R a c)
    (f : HRelIso R G H) (g : HRelIso R H K) : HRelIso R G K where
  vertices := f.vertices.trans g.vertices
  edges := f.edges.trans g.edges
  vertex_label v := (g.vertex_label _).trans (f.vertex_label v)
  edge_label e := tr (f.edge_label e) (g.edge_label _)
  input := by
    change (List.ofFn G.input).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.input,g.input]
  output := by
    change (List.ofFn G.output).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.output,g.output]
  source e := by
    change (G.source e).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.source,g.source]; rfl
  target e := by
    change (G.target e).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.target,g.target]; rfl
end HRelIso
end Hypernets.Graph.SetNet

namespace Hypernets.Graph.NamedNet
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
/-- Normalizing a named graph and naming it again preserves its ordered graph. -/
noncomputable def roundtrip (G : NamedNet σ I O) (a b : Nat) :
    SetNet.HRelIso Eq G.toSet (ofSet G.toSet.toNet.toSet a b).toSet :=
  SetNet.HRelIso.trans Eq.trans (SetNet.HRelIso.ofIso (Net.set_roundtrip G.toSet))
    (SetNet.HRelIso.ofRelIso (ofSet_iso G.toSet.toNet.toSet a b))
end Hypernets.Graph.NamedNet

namespace Hypernets.Graph.SetNet.HRelIso
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op}
    {R S T : Op → Op → Prop} {I O I' O' I'' O''}
    {G : SetNet σ I O} {H : SetNet σ I' O'} {K : SetNet σ I'' O''}

/-- Compose isomorphisms while composing their label relations. -/
def comp (tr : ∀ {a b c}, R a b → S b c → T a c)
    (f : SetNet.HRelIso R G H) (g : SetNet.HRelIso S H K) : SetNet.HRelIso T G K where
  vertices := f.vertices.trans g.vertices
  edges := f.edges.trans g.edges
  vertex_label v := (g.vertex_label _).trans (f.vertex_label v)
  edge_label e := tr (f.edge_label e) (g.edge_label _)
  input := by
    change (List.ofFn G.input).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.input,g.input]
  output := by
    change (List.ofFn G.output).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.output,g.output]
  source e := by
    change (G.source e).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.source,g.source]; rfl
  target e := by
    change (G.target e).map (g.vertices.toFun ∘ f.vertices.toFun) = _
    rw [← List.map_map,f.target,g.target]; rfl

/-- Invert the carrier maps, using symmetry of the edge-label relation. -/
def symm (sy : ∀ {a b}, R a b → R b a) (f : SetNet.HRelIso R G H) : SetNet.HRelIso R H G where
  vertices := f.vertices.symm
  edges := f.edges.symm
  vertex_label v := by simpa [f.vertices.right_inv,Bijection.symm] using (f.vertex_label (f.vertices.invFun v)).symm
  edge_label e := by simpa [f.edges.right_inv,Bijection.symm] using sy (f.edge_label (f.edges.invFun e))
  input := by
    have h := congrArg (List.map f.vertices.invFun) f.input
    simpa [List.map_map,Function.comp_def,f.vertices.left_inv,Bijection.symm] using h.symm
  output := by
    have h := congrArg (List.map f.vertices.invFun) f.output
    simpa [List.map_map,Function.comp_def,f.vertices.left_inv,Bijection.symm] using h.symm
  source e := by
    have h := congrArg (List.map f.vertices.invFun) (f.source (f.edges.invFun e))
    simpa [List.map_map,Function.comp_def,f.vertices.left_inv,f.edges.right_inv,Bijection.symm] using h.symm
  target e := by
    have h := congrArg (List.map f.vertices.invFun) (f.target (f.edges.invFun e))
    simpa [List.map_map,Function.comp_def,f.vertices.left_inv,f.edges.right_inv,Bijection.symm] using h.symm

/-- Apply a signature-preserving label translation to an isomorphism. -/
def relabel {Op' : Type u} (f : SetNet.HRelIso R G H) (τ : Signature L Op')
    (φ : Op → Op') (hi : ∀ p, τ.input (φ p) = σ.input p)
    (ho : ∀ p, τ.output (φ p) = σ.output p) (R' : Op' → Op' → Prop)
    (labels : ∀ {p q}, R p q → R' (φ p) (φ q)) :
    SetNet.HRelIso R' (G.relabel τ φ hi ho) (H.relabel τ φ hi ho) where
  vertices := f.vertices
  edges := f.edges
  vertex_label := f.vertex_label
  edge_label e := labels (f.edge_label e)
  input := f.input
  output := f.output
  source := f.source
  target := f.target

/-- At identical interface types, list preservation gives the indexed boundary equations. -/
def same {G H : SetNet σ I O} (f : SetNet.HRelIso R G H) : SetNet.RelIso R G H where
  vertices := f.vertices
  edges := f.edges
  vertex_label := f.vertex_label
  edge_label := f.edge_label
  input i := by
    have h := congrArg (fun xs => xs[i.val]?) f.input
    simpa [List.map_ofFn,List.getElem?_eq_getElem,i.isLt] using h
  output i := by
    have h := congrArg (fun xs => xs[i.val]?) f.output
    simpa [List.map_ofFn,List.getElem?_eq_getElem,i.isLt] using h
  source := f.source
  target := f.target
end Hypernets.Graph.SetNet.HRelIso

namespace Hypernets.Graph.Net.RelIso
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R : Op → Op → Prop} {G H : Net σ I O}
/-- Expose a typed graph isomorphism as an isomorphism of its full vertex sets. -/
def toSet (f : Net.RelIso R G H) : SetNet.HRelIso R G.toSet H.toSet := SetNet.HRelIso.ofRelIso {
  vertices := Port.bijection f.vertices
  edges := f.edges
  vertex_label := by intro v; cases v with
    | internal v => exact f.internal_label v
    | input i => rfl
    | output j => rfl
  edge_label := f.edge_label
  input := fun _ => rfl
  output := fun _ => rfl
  source := f.source
  target := f.target
}
end Hypernets.Graph.Net.RelIso

namespace Hypernets.Graph.NamedNet
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O I' O'}
    {R : Op → Op → Prop} {G : SetNet σ I O} {H : SetNet σ I' O'}
/-- Independent fresh names on both sides preserve every related-label isomorphism. -/
noncomputable def map_iso (f : SetNet.HRelIso R G H) (a b c d : Nat) :
    SetNet.HRelIso R (ofSet G a b).toSet (ofSet H c d).toSet :=
  SetNet.HRelIso.comp (R := R) (S := Eq) (T := R) (fun h eq => eq ▸ h)
    (SetNet.HRelIso.comp (R := Eq) (S := R) (T := R) (fun eq h => by cases eq; exact h)
      ((SetNet.HRelIso.ofRelIso (ofSet_iso G a b)).symm Eq.symm) f)
    (SetNet.HRelIso.ofRelIso (ofSet_iso H c d))
end Hypernets.Graph.NamedNet

namespace Hypernets.Graph.SetNet.HRelIso
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O}
/-- Identity on an ordered graph for any reflexive label relation. -/
def refl {R : Op → Op → Prop} (re : ∀ p, R p p) (G : SetNet σ I O) : SetNet.HRelIso R G G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  vertex_label _ := rfl
  edge_label e := re _
  input := by simp [Bijection.refl]
  output := by simp [Bijection.refl]
  source e := by simp [Bijection.refl]
  target e := by simp [Bijection.refl]
end Hypernets.Graph.SetNet.HRelIso

namespace Hypernets.Graph.NamedNet
universe u
variable {L : Type} {Op Op' : Type u} {σ : Signature L Op} {I O}
/-- Signature-preserving relabelling retains every actual vertex name. -/
@[reducible] def relabel (G : NamedNet σ I O) (τ : Signature L Op')
    (φ : Op → Op') (hi : ∀ p, τ.input (φ p) = σ.input p)
    (ho : ∀ p, τ.output (φ p) = σ.output p) : NamedNet τ I O where
  names := G.names
  Edge := G.Edge
  finiteEdge := G.finiteEdge
  vertexLabel := G.vertexLabel
  edgeLabel e := φ (G.edgeLabel e)
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
end Hypernets.Graph.NamedNet

namespace Hypernets.Graph.NamedNet
universe u
variable {L : Type} {Op Op' : Type u} {σ : Signature L Op} {I O}
/-- Fresh naming commutes with a signature-preserving change of edge labels. -/
theorem ofSet_relabel (G : SetNet σ I O) (τ : Signature L Op')
    (φ : Op → Op') (hi : ∀ p, τ.input (φ p) = σ.input p)
    (ho : ∀ p, τ.output (φ p) = σ.output p) (a b : Nat) :
    ofSet (G.relabel τ φ hi ho) a b = (ofSet G a b).relabel τ φ hi ho := rfl
end Hypernets.Graph.NamedNet

namespace Hypernets.Graph.SetNet
universe u
variable {L : Type} {Op Op' : Type u} {σ : Signature L Op} {I O}
/-- Pointwise equal translations induce equal relabelled graphs. -/
theorem relabel_congr (G : SetNet σ I O) (τ : Signature L Op')
    (φ ψ : Op → Op') (hi : ∀ p, τ.input (φ p) = σ.input p)
    (ho : ∀ p, τ.output (φ p) = σ.output p)
    (hi' : ∀ p, τ.input (ψ p) = σ.input p)
    (ho' : ∀ p, τ.output (ψ p) = σ.output p) (eq : ∀ p, φ p = ψ p) :
    G.relabel τ φ hi ho = G.relabel τ ψ hi' ho' := by
  have same := funext eq
  cases same
  rfl
end Hypernets.Graph.SetNet
