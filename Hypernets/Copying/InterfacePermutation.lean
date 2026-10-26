import Hypernets.Copying.BoxPermutationPair

/-! Actual interface permutation: move boundary occurrences, preserving all
carriers, edge labels and incidence order. This is not a new term translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.InterfacePermutation
open Graph
variable {d I O} (G : Hypernet d I O) (p : TypedPermutation O)

def ports : Bijection G.Vertex G.Vertex where
  toFun
    | .internal v => .internal v
    | .input i => .input i
    | .output i => .output (p.bijection.toFun i)
  invFun
    | .internal v => .internal v
    | .input i => .input i
    | .output i => .output (p.bijection.invFun i)
  left_inv v := by cases v <;> simp [p.bijection.left_inv]
  right_inv v := by cases v <;> simp [p.bijection.right_inv]

theorem input_iff (v : G.Vertex) : ((ports G p).toFun v).IsInput ↔ v.IsInput := by cases v <;> rfl
theorem output_iff (v : G.Vertex) : ((ports G p).toFun v).IsOutput ↔ v.IsOutput := by cases v <;> rfl

theorem label (v : G.Vertex) : G.vertexLabel ((ports G p).toFun v) = G.vertexLabel v := by
  cases v with
  | internal v => rfl
  | input i => rfl
  | output i => exact p.typed i

/-- Forward-position convention: an old output i moves to output p(i).
The paper's list-reordering convention uses the inverse permutation. -/
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
  input_iff := input_iff G p
  output_iff := output_iff G p
  edge_label e := labelEquiv_refl d _
  source _ := rfl
  target _ := rfl

theorem iso_input (i : Fin I.length) : (iso G p).inputs.toFun i = i := rfl
theorem iso_output (i : Fin O.length) : (iso G p).outputs.toFun i = p.bijection.toFun i := rfl

theorem allLabels_iff (P : Primitive → Prop) : AllLabels P (net G p) ↔ AllLabels P G := Iff.rfl

theorem bindingFree_iff : BindingFree (net G p) ↔ BindingFree G := (iso G p).bindingFree_iff.symm

theorem stable_iff {d O} (G : Hypernet d [.term] O) (p : TypedPermutation O) :
    Stable (net G p) ↔ Stable G := (iso G p).stable_iff.symm

/-- Compensate a known output action, obtaining the original fixed-boundary relation. -/
def compensate {d I O} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (p : TypedPermutation O) (hi : ∀ i, f.inputs.toFun i = i)
    (ho : ∀ i, f.outputs.toFun i = p.bijection.toFun i) :
    DeepIso G (net H p.symm) :=
  (f.trans (iso H p.symm)).toDeepIso
    (fun i => by
      apply Port.input.inj (Internal := (net H p.symm).Internal) (outputs := O.length)
      dsimp only [BoundaryIso.inputs]
      rw [← BoundaryIso.map_input]
      change (ports H p.symm).toFun (f.ports.toFun (.input i)) = .input i
      rw [f.map_input]
      change Port.input (f.inputs.toFun i) = Port.input i
      rw [hi])
    (fun i => by
      apply Port.output.inj (Internal := (net H p.symm).Internal) (inputs := I.length)
      dsimp only [BoundaryIso.outputs]
      rw [← BoundaryIso.map_output]
      change (ports H p.symm).toFun (f.ports.toFun (.output i)) = .output i
      rw [f.map_output]
      change Port.output (p.bijection.invFun (f.outputs.toFun i)) = Port.output i
      rw [ho]
      exact congrArg Port.output (p.bijection.left_inv i))

/-- Applying a permutation and its inverse restores the graph up to carrier isomorphism. -/
def roundtrip : DeepIso G (net (net G p) p.symm) :=
  compensate (iso G p) p (iso_input G p) (iso_output G p)

/-- The same interface permutation on two fixed-boundary isomorphic graphs. -/
def congr {d I O} {G H : Hypernet d I O} (f : DeepIso G H) (p : TypedPermutation O) :
    DeepIso (net G p) (net H p) := by
  let q := (iso G p).symm.trans ((BoundaryIso.ofDeepIso f).trans (iso H p))
  apply q.toDeepIso
  · intro i
    apply Port.input.inj (Internal := H.Internal) (outputs := O.length)
    dsimp only [BoundaryIso.inputs]
    rw [← q.map_input]
    rfl
  · intro i
    apply Port.output.inj (Internal := H.Internal) (inputs := I.length)
    dsimp only [BoundaryIso.outputs]
    rw [← q.map_output]
    change Port.output (p.bijection.toFun (p.bijection.invFun i)) = Port.output i
    rw [p.bijection.right_inv]
end Hypernets.Copying.InterfacePermutation
