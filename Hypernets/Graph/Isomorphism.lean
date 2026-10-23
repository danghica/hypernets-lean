import Hypernets.Graph.Paths

/-! Renaming, graph isomorphism, and invariance of paths under renaming. -/

namespace Hypernets.Graph

namespace Port

def bijection {V W : Type} {n m : Nat} (f : Bijection V W) :
    Bijection (Port V n m) (Port W n m) where
  toFun := map f.toFun
  invFun := map f.invFun
  left_inv v := by cases v <;> simp [map, f.left_inv]
  right_inv v := by cases v <;> simp [map, f.right_inv]

@[simp] theorem map_id {V : Type} {n m : Nat} (v : Port V n m) : map id v = v := by
  cases v <;> rfl

@[simp] theorem map_id_fun {V : Type} {n m : Nat} :
    map (id : V → V) = (id : Port V n m → Port V n m) := funext map_id

end Port

namespace Net

universe u

variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

namespace Reindex

variable (G : Net σ I O) {V E : Type}
    (vertices : Bijection G.Internal V) (edges : Bijection G.Edge E)

def source (e : E) : List (Port V I.length O.length) :=
  (G.source (edges.invFun e)).map (Port.map vertices.toFun)

def target (e : E) : List (Port V I.length O.length) :=
  (G.target (edges.invFun e)).map (Port.map vertices.toFun)

theorem source_unique {v : Port V I.length O.length} {e f : E}
    (he : v ∈ source G vertices edges e) (hf : v ∈ source G vertices edges f) : e = f := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
  have ab := (Port.bijection vertices).injective eq
  subst b
  have same := congrArg edges.toFun (G.source_unique ha hb)
  simpa [edges.right_inv] using same

theorem target_unique {v : Port V I.length O.length} {e f : E}
    (he : v ∈ target G vertices edges e) (hf : v ∈ target G vertices edges f) : e = f := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
  have ab := (Port.bijection vertices).injective eq
  subst b
  have same := congrArg edges.toFun (G.target_unique ha hb)
  simpa [edges.right_inv] using same

theorem source_coverage (v : Port V I.length O.length) :
    (∃ e, v ∈ source G vertices edges e) ↔ ¬ v.IsOutput := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    simpa using G.source_not_output ha
  · intro hv
    have h : ¬ (Port.map vertices.invFun v).IsOutput := by simpa using hv
    obtain ⟨e, he⟩ := (G.source_coverage _).mpr h
    refine ⟨edges.toFun e, List.mem_map.mpr ⟨Port.map vertices.invFun v, ?_, ?_⟩⟩
    · simpa [edges.left_inv] using he
    · exact (Port.bijection vertices).right_inv v

theorem target_coverage (v : Port V I.length O.length) :
    (∃ e, v ∈ target G vertices edges e) ↔ ¬ v.IsInput := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    simpa using G.target_not_input ha
  · intro hv
    have h : ¬ (Port.map vertices.invFun v).IsInput := by simpa using hv
    obtain ⟨e, he⟩ := (G.target_coverage _).mpr h
    refine ⟨edges.toFun e, List.mem_map.mpr ⟨Port.map vertices.invFun v, ?_, ?_⟩⟩
    · simpa [edges.left_inv] using he
    · exact (Port.bijection vertices).right_inv v

theorem label_map (v : G.Vertex) :
    Port.label (fun w => G.internalLabel (vertices.invFun w)) (Port.map vertices.toFun v) =
      G.vertexLabel v := by
  cases v <;> simp [Port.label, Port.map, vertexLabel, vertices.left_inv]

end Reindex

/-- Both carriers can be renamed arbitrarily, while boundary order is fixed.
The resulting object again proves every graph invariant. -/
@[reducible] def reindex (G : Net σ I O) {V E : Type}
    (vertices : Bijection G.Internal V) (edges : Bijection G.Edge E) : Net σ I O where
  Internal := V
  Edge := E
  finiteInternal := vertices.enumeration G.finiteInternal
  finiteEdge := edges.enumeration G.finiteEdge
  internalLabel v := G.internalLabel (vertices.invFun v)
  edgeLabel e := G.edgeLabel (edges.invFun e)
  source := Reindex.source G vertices edges
  target := Reindex.target G vertices edges
  source_nodup e := nodup_map_on (G.source_nodup _) (fun _ _ _ _ h =>
    (Port.bijection vertices).injective h)
  target_nodup e := nodup_map_on (G.target_nodup _) (fun _ _ _ _ h =>
    (Port.bijection vertices).injective h)
  source_unique := Reindex.source_unique G vertices edges
  target_unique := Reindex.target_unique G vertices edges
  source_coverage := Reindex.source_coverage G vertices edges
  target_coverage := Reindex.target_coverage G vertices edges
  source_typed := by
    intro e
    simp only [Reindex.source, List.map_map, Function.comp_def]
    have eq := funext (Reindex.label_map G vertices)
    rw [eq]; exact G.source_typed _
  target_typed := by
    intro e
    simp only [Reindex.target, List.map_map, Function.comp_def]
    have eq := funext (Reindex.label_map G vertices)
    rw [eq]; exact G.target_typed _

structure Iso (G H : Net σ I O) where
  vertices : Bijection G.Internal H.Internal
  edges : Bijection G.Edge H.Edge
  internal_label : ∀ v, H.internalLabel (vertices.toFun v) = G.internalLabel v
  edge_label : ∀ e, H.edgeLabel (edges.toFun e) = G.edgeLabel e
  source : ∀ e, (G.source e).map (Port.map vertices.toFun) = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map (Port.map vertices.toFun) = H.target (edges.toFun e)

namespace Iso

variable {G H K : Net σ I O}

def refl (G : Net σ I O) : Iso G G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := rfl
  source e := by simp [Bijection.refl]
  target e := by simp [Bijection.refl]

def symm (f : Iso G H) : Iso H G where
  vertices := f.vertices.symm
  edges := f.edges.symm
  internal_label v := by simpa [Bijection.symm, f.vertices.right_inv] using (f.internal_label (f.vertices.invFun v)).symm
  edge_label e := by simpa [Bijection.symm, f.edges.right_inv] using (f.edge_label (f.edges.invFun e)).symm
  source e := by
    have h := congrArg (List.map (Port.map f.vertices.invFun)) (f.source (f.edges.invFun e))
    have inv : ∀ v : G.Vertex, Port.map f.vertices.invFun (Port.map f.vertices.toFun v) = v :=
      (Port.bijection f.vertices).left_inv
    simpa [List.map_map, Function.comp_def, inv, f.edges.right_inv, Bijection.symm] using h.symm
  target e := by
    have h := congrArg (List.map (Port.map f.vertices.invFun)) (f.target (f.edges.invFun e))
    have inv : ∀ v : G.Vertex, Port.map f.vertices.invFun (Port.map f.vertices.toFun v) = v :=
      (Port.bijection f.vertices).left_inv
    simpa [List.map_map, Function.comp_def, inv, f.edges.right_inv, Bijection.symm] using h.symm

def trans (f : Iso G H) (g : Iso H K) : Iso G K where
  vertices := f.vertices.trans g.vertices
  edges := f.edges.trans g.edges
  internal_label v := (g.internal_label _).trans (f.internal_label v)
  edge_label e := (g.edge_label _).trans (f.edge_label e)
  source e := by
    calc
      _ = ((G.source e).map (Port.map f.vertices.toFun)).map (Port.map g.vertices.toFun) := by
        rw [List.map_map]
        congr 1; funext v; cases v <;> rfl
      _ = _ := by rw [f.source, g.source]; rfl
  target e := by
    calc
      _ = ((G.target e).map (Port.map f.vertices.toFun)).map (Port.map g.vertices.toFun) := by
        rw [List.map_map]
        congr 1; funext v; cases v <;> rfl
      _ = _ := by rw [f.target, g.target]; rfl

theorem adjacent_iff (f : Iso G H) (e e' : G.Edge) :
    H.Adjacent (f.edges.toFun e) (f.edges.toFun e') ↔ G.Adjacent e e' := by
  constructor
  · rintro ⟨v, hv, hw⟩
    rw [← f.target] at hv
    rw [← f.source] at hw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hw
    have ab := (Port.bijection f.vertices).injective eq
    subst b
    exact ⟨a, ha, hb⟩
  · rintro ⟨v, hv, hw⟩
    refine ⟨Port.map f.vertices.toFun v, ?_, ?_⟩
    · rw [← f.target]; exact List.mem_map_of_mem hv
    · rw [← f.source]; exact List.mem_map_of_mem hw

theorem path_iff (f : Iso G H) (es : List G.Edge) :
    H.Path (es.map f.edges.toFun) ↔ G.Path es :=
  path_map_iff f.edges.toFun f.adjacent_iff es

end Iso

def reindexIso (G : Net σ I O) {V E : Type}
    (vertices : Bijection G.Internal V) (edges : Bijection G.Edge E) :
    Iso G (G.reindex vertices edges) where
  vertices := vertices
  edges := edges
  internal_label v := congrArg G.internalLabel (vertices.left_inv v)
  edge_label e := congrArg G.edgeLabel (edges.left_inv e)
  source e := by simp [reindex, Reindex.source, edges.left_inv]
  target e := by simp [reindex, Reindex.target, edges.left_inv]

end Net
end Hypernets.Graph
