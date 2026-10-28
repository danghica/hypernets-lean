import Hypernets.Copying.MinimalContractionSpine
import Hypernets.Graph.SetPresentation

/-! A forward-closed selection of sharing edges is again a concrete contraction
 tree once its newly exposed inputs are enumerated. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree
open Graph Opening

structure Selection {s : ShareSort} {m : Nat} (T : ContractionTree s m) where
  chosen : T.net.Edge → Prop
  forward : ∀ {e f}, chosen e → T.net.Adjacent e f → chosen f
  root : chosen T.root

namespace Selection
variable {s : ShareSort} {m : Nat} {T : ContractionTree s m} (S : Selection T)

def Incident (v : T.net.Vertex) : Prop :=
  ∃ e, S.chosen e ∧ (v ∈ T.net.source e ∨ v ∈ T.net.target e)

abbrev Vertex := {v : T.net.Vertex // S.Incident v}
abbrev Edge := {e : T.net.Edge // S.chosen e}

def source (e : S.Edge) : List S.Vertex :=
  (T.net.source e.val).attach.map fun v => ⟨v.val,e.val,e.property,Or.inl v.property⟩
def target (e : S.Edge) : List S.Vertex :=
  (T.net.target e.val).attach.map fun v => ⟨v.val,e.val,e.property,Or.inr v.property⟩

@[simp] theorem source_val (e : S.Edge) : (S.source e).map Subtype.val = T.net.source e.val := by
  simp [source,List.map_map]
@[simp] theorem target_val (e : S.Edge) : (S.target e).map Subtype.val = T.net.target e.val := by
  simp [target,List.map_map]

@[simp] theorem mem_source (v : S.Vertex) (e : S.Edge) :
    v ∈ S.source e ↔ v.val ∈ T.net.source e.val := by
  constructor
  · intro h; have hm := List.mem_map_of_mem (f := Subtype.val) h
    rw [S.source_val] at hm
    exact hm
  · intro h
    exact List.mem_map.mpr ⟨⟨v.val,h⟩,List.mem_attach ..,Subtype.ext rfl⟩
@[simp] theorem mem_target (v : S.Vertex) (e : S.Edge) :
    v ∈ S.target e ↔ v.val ∈ T.net.target e.val := by
  constructor
  · intro h; have hm := List.mem_map_of_mem (f := Subtype.val) h
    rw [S.target_val] at hm
    exact hm
  · intro h
    exact List.mem_map.mpr ⟨⟨v.val,h⟩,List.mem_attach ..,Subtype.ext rfl⟩

def Input (v : S.Vertex) : Prop := ¬ ∃ e : S.Edge, v ∈ S.target e

def output : S.Vertex := ⟨.output 0,T.root,S.root,Or.inr T.root_output⟩

theorem label (v : S.Vertex) : T.net.vertexLabel v.val = s.wire := by
  obtain ⟨e,_,hv | hv⟩ := v.property
  · have typed := List.mem_map_of_mem (f := T.net.vertexLabel) hv
    change _ ∈ (T.net.source e).map (Port.label T.net.internalLabel) at typed
    rw [T.net.source_typed] at typed
    rcases T.labels e with h | h <;> rw [h] at typed
    · exact False.elim (List.not_mem_nil typed)
    · simpa [primitiveSignature] using typed
  · have typed := List.mem_map_of_mem (f := T.net.vertexLabel) hv
    change _ ∈ (T.net.target e).map (Port.label T.net.internalLabel) at typed
    rw [T.net.target_typed] at typed
    rcases T.labels e with h | h <;> rw [h] at typed <;>
      simpa [primitiveSignature] using typed

theorem source_coverage (v : S.Vertex) :
    (∃ e : S.Edge, v ∈ S.source e) ↔ v ≠ S.output := by
  constructor
  · rintro ⟨e,h⟩ eq
    have source := (S.mem_source v e).mp h
    rw [eq] at source
    exact T.net.source_not_output source trivial
  · intro different
    obtain ⟨e,selected,h | h⟩ := v.property
    · exact ⟨⟨e,selected⟩,(S.mem_source ..).mpr h⟩
    · have notOutput : ¬ v.val.IsOutput := by
        cases eq : v.val with
        | internal x => simp [Port.IsOutput]
        | input i => simp [Port.IsOutput]
        | output i =>
          have zero : i = 0 := Fin.ext (by change i.val = 0; have := i.isLt; change i.val < 1 at this; omega)
          exact False.elim (different (Subtype.ext (eq.trans (congrArg Port.output zero))))
      obtain ⟨f,hf⟩ := (T.net.source_coverage v.val).mpr notOutput
      exact ⟨⟨f,S.forward selected ⟨v.val,h,hf⟩⟩,(S.mem_source ..).mpr hf⟩

theorem output_not_input : ¬ S.Input S.output := by
  intro h
  exact h ⟨⟨T.root,S.root⟩,(S.mem_target ..).mpr T.root_output⟩

/-- Normalize a selected tree after an explicit complete ordering of its boundary. -/
noncomputable def setNet (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v) :
    SetNet primitiveSignature (List.replicate inputs.length s.wire) [s.wire] where
  Vertex := S.Vertex
  Edge := S.Edge
  finiteVertex := T.net.toSet.finiteVertex.subtype S.Incident
  finiteEdge := T.net.finiteEdge.subtype S.chosen
  vertexLabel v := T.net.vertexLabel v.val
  edgeLabel e := T.net.edgeLabel e.val
  input i := inputs.get ⟨i.val,by simpa using i.isLt⟩
  output _ := S.output
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
    have nd := T.net.source_nodup e.val
    rw [← S.source_val e] at nd
    exact nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj) (by simpa only [List.getElem_map] using congrArg Subtype.val eq)
  target_nodup e := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    have nd := T.net.target_nodup e.val
    rw [← S.target_val e] at nd
    exact nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj) (by simpa only [List.getElem_map] using congrArg Subtype.val eq)
  source_unique := by
    intro v e f he hf
    exact Subtype.ext (T.net.source_unique ((S.mem_source ..).mp he) ((S.mem_source ..).mp hf))
  target_unique := by
    intro v e f he hf
    exact Subtype.ext (T.net.target_unique ((S.mem_target ..).mp he) ((S.mem_target ..).mp hf))
  source_coverage v := by
    rw [S.source_coverage]
    constructor
    · rintro neq ⟨j,h⟩; exact neq h.symm
    · intro h eq; exact h ⟨0,eq.symm⟩
  target_coverage v := by
    classical
    have inputiff : (∃ i : Fin (List.replicate inputs.length s.wire).length,
        inputs.get ⟨i.val,by simpa using i.isLt⟩ = v) ↔ v ∈ inputs := by
      constructor
      · rintro ⟨i,rfl⟩; exact List.get_mem ..
      · intro h; obtain ⟨i,hi⟩ := List.get_of_mem h
        exact ⟨⟨i.val,by simp⟩,hi⟩
    rw [inputiff,boundary]
    exact Classical.not_not.symm
  source_typed e := by
    have := T.net.source_typed e.val
    rw [← S.source_val e] at this
    simpa only [List.map_map,Function.comp_def,Net.vertexLabel] using this
  target_typed e := by
    have := T.net.target_typed e.val
    rw [← S.target_val e] at this
    simpa only [List.map_map,Function.comp_def,Net.vertexLabel] using this

variable (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)

/-- The exact inclusion of normalized selected vertices into the original graph. -/
noncomputable def ports (v : (S.setNet inputs distinct boundary).toNet.Vertex) : T.net.Vertex :=
  ((S.setNet inputs distinct boundary).decode v).val

theorem source_ports (e : S.Edge) :
    ((S.setNet inputs distinct boundary).toNet.source e).map (S.ports inputs distinct boundary) =
      T.net.source e.val := by
  change ((S.source e).map (S.setNet inputs distinct boundary).encode).map _ = _
  simp only [List.map_map,Function.comp_def,ports,SetNet.decode_encode]
  exact S.source_val e

theorem target_ports (e : S.Edge) :
    ((S.setNet inputs distinct boundary).toNet.target e).map (S.ports inputs distinct boundary) =
      T.net.target e.val := by
  change ((S.target e).map (S.setNet inputs distinct boundary).encode).map _ = _
  simp only [List.map_map,Function.comp_def,ports,SetNet.decode_encode]
  exact S.target_val e

theorem adjacent {e f : S.Edge}
    (h : (S.setNet inputs distinct boundary).toNet.Adjacent e f) :
    T.net.Adjacent e.val f.val := by
  obtain ⟨v,hv,hw⟩ := h
  refine ⟨S.ports inputs distinct boundary v,?_,?_⟩
  · rw [← S.target_ports inputs distinct boundary e]
    exact List.mem_map_of_mem hv
  · rw [← S.source_ports inputs distinct boundary f]
    exact List.mem_map_of_mem hw

/-- A selected component, including its actual side-boundary order, is a tree. -/
noncomputable def tree : ContractionTree s inputs.length where
  net := (S.setNet inputs distinct boundary).toNet
  labels e := T.labels e.val
  acyclic := by
    intro es h
    have nd := T.acyclic (h.map Subtype.val (fun adj => S.adjacent inputs distinct boundary adj))
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    exact nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
      (by simpa only [List.getElem_map] using congrArg Subtype.val eq)

/-- The selected subtree is a full-label local occurrence, not just a graph map. -/
noncomputable def occurrence (d : Nat) :
    Occurrence ((S.tree inputs distinct boundary).atDepth d) (T.atDepth d) :=
  (show MatchEmbedding ((S.tree inputs distinct boundary).atDepth d) (T.atDepth d) from {
    ports := S.ports inputs distinct boundary
    edges := Subtype.val
    edge_injective := fun _ _ h => Subtype.ext h
    primitive := fun _ _ h => h
    source := S.source_ports inputs distinct boundary
    target := S.target_ports inputs distinct boundary
  }).occurrence (fun _ => labelEquiv_refl _ _)

theorem occurrence_input (d : Nat) (i : Fin (List.replicate inputs.length s.wire).length) :
    (S.occurrence inputs distinct boundary d).ports (.input i) =
      (inputs.get ⟨i.val,by simpa using i.isLt⟩).val := rfl

theorem occurrence_output (d : Nat) :
    (S.occurrence inputs distinct boundary d).ports (.output 0) = .output 0 := rfl

end Selection
end Hypernets.Copying.ContractionTree
