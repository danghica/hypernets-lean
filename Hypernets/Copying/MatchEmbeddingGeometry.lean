import Hypernets.Copying.MatchEmbedding

/-! The internal geometry of an incidence-preserving graph occurrence.
Boundary attachment may identify an input with an output.  It cannot identify
two ports having the same polarity, or identify an internal port with any
other port.  Complete recursive label matching also recovers wire typing. -/
namespace Hypernets.Copying
open Graph

namespace MatchEmbedding

private theorem map_injective_on_of_nodup {α β : Type} {xs : List α} {f : α → β}
    (h : (xs.map f).Nodup) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs)
    (eq : f a = f b) : a = b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  have hij : i = j := h.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
    (by simpa using eq)
  subst j
  rfl

variable {d r I O J K} {A : Hypernet d I O} {G : Hypernet r J K}

/-- Two ports that have consumers cannot be identified by an occurrence. -/
theorem ports_injective_of_not_output (f : MatchEmbedding A G) {v w : A.Vertex}
    (hv : ¬v.IsOutput) (hw : ¬w.IsOutput) (eq : f.ports v = f.ports w) : v = w := by
  obtain ⟨e, he⟩ := (A.source_coverage v).mpr hv
  obtain ⟨b, hb⟩ := (A.source_coverage w).mpr hw
  have edges : e = b := f.edge_injective
    (G.source_unique (f.source_mem he) (eq ▸ f.source_mem hb))
  subst b
  have nd : ((A.source e).map f.ports).Nodup := by rw [f.source]; exact G.source_nodup _
  exact map_injective_on_of_nodup nd he hb eq

/-- Two ports that have producers cannot be identified by an occurrence. -/
theorem ports_injective_of_not_input (f : MatchEmbedding A G) {v w : A.Vertex}
    (hv : ¬v.IsInput) (hw : ¬w.IsInput) (eq : f.ports v = f.ports w) : v = w := by
  obtain ⟨e, he⟩ := (A.target_coverage v).mpr hv
  obtain ⟨b, hb⟩ := (A.target_coverage w).mpr hw
  have edges : e = b := f.edge_injective
    (G.target_unique (f.target_mem he) (eq ▸ f.target_mem hb))
  subst b
  have nd : ((A.target e).map f.ports).Nodup := by rw [f.target]; exact G.target_nodup _
  exact map_injective_on_of_nodup nd he hb eq

/-- An internal port has both incidences and therefore stays internal. -/
theorem exists_internal (f : MatchEmbedding A G) (a : A.Internal) :
    ∃ b : G.Internal, f.ports (.internal a) = .internal b := by
  obtain ⟨e, he⟩ := (A.source_coverage (.internal a)).mpr (by simp [Port.IsOutput])
  obtain ⟨b, hb⟩ := (A.target_coverage (.internal a)).mpr (by simp [Port.IsInput])
  have hs := G.source_not_output (f.source_mem he)
  have ht := G.target_not_input (f.target_mem hb)
  cases h : f.ports (.internal a) with
  | internal v => exact ⟨v, rfl⟩
  | input i => simp [h, Port.IsInput] at ht
  | output i => simp [h, Port.IsOutput] at hs

/-- The induced map on internal carriers. -/
noncomputable def internal (f : MatchEmbedding A G) (a : A.Internal) : G.Internal :=
  Classical.choose (f.exists_internal a)

@[simp] theorem ports_internal (f : MatchEmbedding A G) (a : A.Internal) :
    f.ports (.internal a) = .internal (f.internal a) :=
  Classical.choose_spec (f.exists_internal a)

/-- An internal image cannot alias any different source port, including a boundary port. -/
theorem ports_eq_internal_iff (f : MatchEmbedding A G) {v : A.Vertex} {a : A.Internal} :
    f.ports v = .internal (f.internal a) ↔ v = .internal a := by
  constructor
  · intro h
    have eq : f.ports v = f.ports (.internal a) := h.trans (f.ports_internal a).symm
    cases v with
    | internal b =>
      exact f.ports_injective_of_not_output (v := .internal b) (w := .internal a)
        (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) eq
    | input i =>
      exact f.ports_injective_of_not_output (v := .input i) (w := .internal a)
        (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) eq
    | output i =>
      exact f.ports_injective_of_not_input (v := .output i) (w := .internal a)
        (by simp [Port.IsInput]) (by simp [Port.IsInput]) eq
  · rintro rfl
    exact f.ports_internal a

theorem internal_injective (f : MatchEmbedding A G) : Function.Injective f.internal := by
  intro a b h
  have eq : f.ports (.internal a) = .internal (f.internal b) :=
    (f.ports_internal a).trans (congrArg Port.internal h)
  exact Port.internal.inj (f.ports_eq_internal_iff.mp eq)

/-- Full recursive label matching determines wire types from their incidences. -/
theorem vertexLabel {G : Hypernet d J K} (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (v : A.Vertex) : G.vertexLabel (f.ports v) = A.vertexLabel v := by
  have source : ∀ e, (A.source e).map (G.vertexLabel ∘ f.ports) =
      (A.source e).map A.vertexLabel := by
    intro e
    rw [← List.map_map, f.source]
    exact (G.source_typed _).trans
      ((labelEquiv_input d (labels e)).symm.trans (A.source_typed e).symm)
  have target : ∀ e, (A.target e).map (G.vertexLabel ∘ f.ports) =
      (A.target e).map A.vertexLabel := by
    intro e
    rw [← List.map_map, f.target]
    exact (G.target_typed _).trans
      ((labelEquiv_output d (labels e)).symm.trans (A.target_typed e).symm)
  cases v with
  | internal a =>
    obtain ⟨e, he⟩ := (A.source_coverage (.internal a)).mpr (by simp [Port.IsOutput])
    exact List.map_inj_left.mp (source e) _ he
  | input i =>
    obtain ⟨e, he⟩ := (A.source_coverage (.input i)).mpr (by simp [Port.IsOutput])
    exact List.map_inj_left.mp (source e) _ he
  | output i =>
    obtain ⟨e, he⟩ := (A.target_coverage (.output i)).mpr (by simp [Port.IsInput])
    exact List.map_inj_left.mp (target e) _ he

end MatchEmbedding
end Hypernets.Copying
