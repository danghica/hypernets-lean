import Hypernets.Graph.RootedBasin
import Hypernets.Graph.PathRank

/-! Normalize a finite forward-convergent host component at its actual exit. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.RootedBasin
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {G : Net σ I O} {sort : L} (S : Net.RootedBasin G sort)

def Incident (v : G.Vertex) : Prop :=
  ∃ e, S.chosen e ∧ (v ∈ G.source e ∨ v ∈ G.target e)

abbrev Vertex := {v : G.Vertex // S.Incident v}
abbrev Edge := {e : G.Edge // S.chosen e}

def source (e : S.Edge) : List S.Vertex :=
  (G.source e.val).attach.map fun v => ⟨v.val,e.val,e.property,Or.inl v.property⟩
def target (e : S.Edge) : List S.Vertex :=
  (G.target e.val).attach.map fun v => ⟨v.val,e.val,e.property,Or.inr v.property⟩

@[simp] theorem source_val (e : S.Edge) : (S.source e).map Subtype.val = G.source e.val := by
  simp [source,List.map_map]
@[simp] theorem target_val (e : S.Edge) : (S.target e).map Subtype.val = G.target e.val := by
  simp [target,List.map_map]

@[simp] theorem mem_source (v : S.Vertex) (e : S.Edge) :
    v ∈ S.source e ↔ v.val ∈ G.source e.val := by
  constructor
  · intro h; have hm := List.mem_map_of_mem (f := Subtype.val) h
    rw [S.source_val] at hm
    exact hm
  · intro h
    exact List.mem_map.mpr ⟨⟨v.val,h⟩,List.mem_attach ..,Subtype.ext rfl⟩
@[simp] theorem mem_target (v : S.Vertex) (e : S.Edge) :
    v ∈ S.target e ↔ v.val ∈ G.target e.val := by
  constructor
  · intro h; have hm := List.mem_map_of_mem (f := Subtype.val) h
    rw [S.target_val] at hm
    exact hm
  · intro h
    exact List.mem_map.mpr ⟨⟨v.val,h⟩,List.mem_attach ..,Subtype.ext rfl⟩

def Input (v : S.Vertex) : Prop := ¬ ∃ e : S.Edge, v ∈ S.target e

def exit : S.Vertex := ⟨S.output,S.root,S.root_chosen,Or.inr (by rw [S.root_target]; simp)⟩

theorem label (v : S.Vertex) : G.vertexLabel v.val = sort := by
  obtain ⟨e,chosen,h | h⟩ := v.property
  · exact S.source_label e chosen v.val h
  · exact S.target_label e chosen v.val h

theorem source_coverage (v : S.Vertex) :
    (∃ e : S.Edge, v ∈ S.source e) ↔ v ≠ S.exit := by
  constructor
  · rintro ⟨e,h⟩ eq
    have source := (S.mem_source v e).mp h
    have same : v.val = S.output := congrArg Subtype.val eq
    exact S.output_not_source e (same ▸ source)
  · intro different
    obtain ⟨e,selected,h | h⟩ := v.property
    · exact ⟨⟨e,selected⟩,(S.mem_source ..).mpr h⟩
    · have ne : e ≠ S.root := by
        intro eq
        subst e
        rw [S.root_target] at h
        have same : v.val = S.output := by simpa using h
        exact different (Subtype.ext same)
      obtain ⟨f,chosen,w,prod,cons⟩ := S.next_of_ne selected ne
      have eq : v.val = w := by
        have single := S.single e selected
        cases row : G.target e with
        | nil => simp [row] at h
        | cons a tail =>
          have empty : tail = [] := by simpa [row] using single
          subst tail
          have va : v.val = a := by simpa [row] using h
          have wa : w = a := by simpa [row] using prod
          exact va.trans wa.symm
      exact ⟨⟨f,chosen⟩,(S.mem_source ..).mpr (eq ▸ cons)⟩

theorem output_not_input : ¬ S.Input S.exit := by
  intro h
  exact h ⟨⟨S.root,S.root_chosen⟩,(S.mem_target ..).mpr (by rw [S.root_target]; simp [exit])⟩

/-- Normalize a selected tree after an explicit complete ordering of its boundary. -/
noncomputable def setNet (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v) :
    SetNet σ (List.replicate inputs.length sort) [sort] where
  Vertex := S.Vertex
  Edge := S.Edge
  finiteVertex := G.toSet.finiteVertex.subtype S.Incident
  finiteEdge := G.finiteEdge.subtype S.chosen
  vertexLabel v := G.vertexLabel v.val
  edgeLabel e := G.edgeLabel e.val
  input i := inputs.get ⟨i.val,by simpa using i.isLt⟩
  output _ := S.exit
  input_injective := by
    intro i j eq; apply Fin.ext
    exact distinct.eq_of_getElem_eq (by simpa using i.isLt) (by simpa using j.isLt) eq
  output_injective := by intro i j _; apply Fin.ext; have := i.isLt; have := j.isLt; simp only [List.length_singleton] at *; omega
  disjoint := by
    intro i j eq
    have h := (boundary _).mp (List.get_mem inputs ⟨i.val,by simpa using i.isLt⟩)
    exact S.output_not_input (eq ▸ h)
  input_label i := by rw [S.label]; simp
  output_label i := by
    rw [S.label]
    have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    have zero : i = 0 := Fin.ext hi
    subst i
    rfl
  source := S.source
  target := S.target
  source_nodup e := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    have nd := G.source_nodup e.val
    rw [← S.source_val e] at nd
    exact nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj) (by simpa only [List.getElem_map] using congrArg Subtype.val eq)
  target_nodup e := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    have nd := G.target_nodup e.val
    rw [← S.target_val e] at nd
    exact nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj) (by simpa only [List.getElem_map] using congrArg Subtype.val eq)
  source_unique := by
    intro v e f he hf
    exact Subtype.ext (G.source_unique ((S.mem_source ..).mp he) ((S.mem_source ..).mp hf))
  target_unique := by
    intro v e f he hf
    exact Subtype.ext (G.target_unique ((S.mem_target ..).mp he) ((S.mem_target ..).mp hf))
  source_coverage v := by
    rw [S.source_coverage]
    constructor
    · rintro neq ⟨j,h⟩; exact neq h.symm
    · intro h eq; exact h ⟨0,eq.symm⟩
  target_coverage v := by
    classical
    have inputiff : (∃ i : Fin (List.replicate inputs.length sort).length,
        inputs.get ⟨i.val,by simpa using i.isLt⟩ = v) ↔ v ∈ inputs := by
      constructor
      · rintro ⟨i,rfl⟩; exact List.get_mem ..
      · intro h; obtain ⟨i,hi⟩ := List.get_of_mem h
        exact ⟨⟨i.val,by simp⟩,hi⟩
    rw [inputiff,boundary]
    exact Classical.not_not.symm
  source_typed e := by
    have := G.source_typed e.val
    rw [← S.source_val e] at this
    simpa only [List.map_map,Function.comp_def,Net.vertexLabel] using this
  target_typed e := by
    have := G.target_typed e.val
    rw [← S.target_val e] at this
    simpa only [List.map_map,Function.comp_def,Net.vertexLabel] using this

variable (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)

/-- The exact inclusion of normalized selected vertices into the original graph. -/
noncomputable def ports (v : (S.setNet inputs distinct boundary).toNet.Vertex) : G.Vertex :=
  ((S.setNet inputs distinct boundary).decode v).val

theorem source_ports (e : S.Edge) :
    ((S.setNet inputs distinct boundary).toNet.source e).map (S.ports inputs distinct boundary) =
      G.source e.val := by
  change ((S.source e).map (S.setNet inputs distinct boundary).encode).map _ = _
  simp only [List.map_map,Function.comp_def,ports,SetNet.decode_encode]
  exact S.source_val e

theorem target_ports (e : S.Edge) :
    ((S.setNet inputs distinct boundary).toNet.target e).map (S.ports inputs distinct boundary) =
      G.target e.val := by
  change ((S.target e).map (S.setNet inputs distinct boundary).encode).map _ = _
  simp only [List.map_map,Function.comp_def,ports,SetNet.decode_encode]
  exact S.target_val e

theorem adjacent {e f : S.Edge}
    (h : (S.setNet inputs distinct boundary).toNet.Adjacent e f) :
    G.Adjacent e.val f.val := by
  obtain ⟨v,hv,hw⟩ := h
  refine ⟨S.ports inputs distinct boundary v,?_,?_⟩
  · rw [← S.target_ports inputs distinct boundary e]
    exact List.mem_map_of_mem hv
  · rw [← S.source_ports inputs distinct boundary f]
    exact List.mem_map_of_mem hw


/-- Every selected forward step strictly decreases the actual terminal distance. -/
theorem distance_decreases {e f : S.Edge}
    (h : (S.setNet inputs distinct boundary).toNet.Adjacent e f) :
    S.distance f < S.distance e := by
  have eq := S.distance_step (S.adjacent inputs distinct boundary h)
  omega

/-- A selected host component is edge-acyclic by its finite distance to the exit. -/
theorem acyclic {es : List S.Edge}
    (path : (S.setNet inputs distinct boundary).toNet.Path es) : es.Nodup := by
  have strict {es : List S.Edge} (path : (S.setNet inputs distinct boundary).toNet.Path es)
      {i j : Nat} (hi : i < es.length) (hj : j < es.length) (ij : i < j) :
      S.distance es[j] < S.distance es[i] := by
    induction es generalizing i j with
    | nil => simp at hi
    | cons e es ih =>
      cases es with
      | nil => simp at hi hj; omega
      | cons f es =>
        obtain ⟨adj,tail⟩ := Net.path_pair_iff.mp path
        have step := S.distance_decreases inputs distinct boundary adj
        cases i with
        | zero =>
          cases j with
          | zero => omega
          | succ j =>
            cases j with
            | zero => exact step
            | succ j =>
              exact Nat.lt_trans
                (ih tail (i := 0) (j := j+1) (by simp) (by simpa using hj) (by omega)) step
        | succ i =>
          cases j with
          | zero => omega
          | succ j => exact ih tail (by simpa using hi) (by simpa using hj) (by omega)
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  by_cases same : i = j
  · exact same
  exfalso
  rcases Nat.lt_or_gt_of_ne same with lt | gt
  · have bad := strict path hi hj lt
    rw [eq] at bad
    exact Nat.lt_irrefl _ bad
  · have bad := strict path hj hi gt
    rw [eq] at bad
    exact Nat.lt_irrefl _ bad

end Hypernets.Graph.Net.RootedBasin
