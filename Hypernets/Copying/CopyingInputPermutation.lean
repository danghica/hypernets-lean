import Hypernets.Copying.BoxPermutationPair

/-! Actual interface permutation: move boundary occurrences, preserving all
carriers, edge labels and incidence order. This is not a new term translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph
variable {d I O} (G : Hypernet d I O) (p : TypedPermutation I)

def ports : Bijection G.Vertex G.Vertex where
  toFun
    | .internal v => .internal v
    | .output i => .output i
    | .input i => .input (p.bijection.toFun i)
  invFun
    | .internal v => .internal v
    | .output i => .output i
    | .input i => .input (p.bijection.invFun i)
  left_inv v := by cases v <;> simp [p.bijection.left_inv]
  right_inv v := by cases v <;> simp [p.bijection.right_inv]

theorem input_iff (v : G.Vertex) : ((ports G p).toFun v).IsInput ↔ v.IsInput := by cases v <;> rfl
theorem output_iff (v : G.Vertex) : ((ports G p).toFun v).IsOutput ↔ v.IsOutput := by cases v <;> rfl

theorem label (v : G.Vertex) : G.vertexLabel ((ports G p).toFun v) = G.vertexLabel v := by
  cases v with
  | internal v => rfl
  | output i => rfl
  | input i => exact p.typed i

/-- Forward-position convention: old input i moves to input p(i).
The source incidences retain every original source-port order. -/
def net : Hypernet d I O where
  Internal := G.Internal
  Edge := G.Edge
  finiteInternal := G.finiteInternal
  finiteEdge := G.finiteEdge
  internalLabel := G.internalLabel
  edgeLabel := G.edgeLabel
  source e := (G.source e).map (ports G p).toFun
  target e := (G.target e).map (ports G p).toFun
  source_nodup e := nodup_map_on (G.source_nodup e) (fun _ _ _ _ h => (ports G p).injective h)
  target_nodup e := nodup_map_on (G.target_nodup e) (fun _ _ _ _ h => (ports G p).injective h)
  source_unique := by
    intro v e f he hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp hf
    have eq := (ports G p).injective eq
    subst b
    exact G.source_unique ha hb
  target_unique := by
    intro v e f he hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp hf
    have eq := (ports G p).injective eq
    subst b
    exact G.target_unique ha hb
  source_coverage v := by
    constructor
    · rintro ⟨e,he⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
      exact fun h => G.source_not_output ha ((output_iff G p a).mp h)
    · intro hv
      have h : ¬ ((ports G p).invFun v).IsOutput := by cases v <;> exact hv
      obtain ⟨e,he⟩ := (G.source_coverage _).mpr h
      exact ⟨e,List.mem_map.mpr ⟨_,he,(ports G p).right_inv v⟩⟩
  target_coverage v := by
    constructor
    · rintro ⟨e,he⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
      exact fun h => G.target_not_input ha ((input_iff G p a).mp h)
    · intro hv
      have h : ¬ ((ports G p).invFun v).IsInput := by cases v <;> exact hv
      obtain ⟨e,he⟩ := (G.target_coverage _).mpr h
      exact ⟨e,List.mem_map.mpr ⟨_,he,(ports G p).right_inv v⟩⟩
  source_typed e := by
    change ((G.source e).map (ports G p).toFun).map G.vertexLabel = _
    simp only [List.map_map,Function.comp_def]
    have eq := funext (label G p)
    rw [eq]
    exact G.source_typed e
  target_typed e := by
    change ((G.target e).map (ports G p).toFun).map G.vertexLabel = _
    simp only [List.map_map,Function.comp_def]
    have eq := funext (label G p)
    rw [eq]
    exact G.target_typed e

/-- The ordered incidence isomorphism records, rather than forgets, the external action. -/
def iso : BoundaryIso G (net G p) where
  ports := ports G p
  edges := Bijection.refl _
  vertex_label := label G p
  output_iff := output_iff G p
  input_iff := input_iff G p
  edge_label e := labelEquiv_refl d _
  source _ := rfl
  target _ := rfl

theorem iso_output (i : Fin O.length) : (iso G p).outputs.toFun i = i := rfl
theorem iso_input (i : Fin I.length) : (iso G p).inputs.toFun i = p.bijection.toFun i := rfl

theorem allLabels_iff (P : Primitive → Prop) : AllLabels P (net G p) ↔ AllLabels P G := Iff.rfl

theorem bindingFree_iff : BindingFree (net G p) ↔ BindingFree G := (iso G p).bindingFree_iff.symm

end Hypernets.Copying.CopyingInputPermutation
