import Hypernets.Graph.Basic

/-!
Typed shallow edge replacement (Appendix B). The replacement's boundary is
identified with the hole's ports; internal vertices are fresh, by construction.
The hole may be a self-loop: the entire replacement map need not be injective.
-/

namespace Hypernets.Graph.Net

universe u

namespace Replacement

variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O) (hole : C.Edge)
    (H : Net σ (σ.input (C.edgeLabel hole)) (σ.output (C.edgeLabel hole)))

abbrev Vertex := Port (C.Internal ⊕ H.Internal) I.length O.length
abbrev Edge := {e : C.Edge // e ≠ hole} ⊕ H.Edge

def host : C.Vertex → Vertex C hole H := Port.map Sum.inl

def insert : H.Vertex → Vertex C hole H
  | .internal v => .internal (.inr v)
  | .input i => host C hole H (C.sourcePort hole i)
  | .output i => host C hole H (C.targetPort hole i)

theorem host_injective {a b : C.Vertex} (h : host C hole H a = host C hole H b) : a = b :=
  Port.map_injective (fun _ _ h => Sum.inl.inj h) h

theorem host_ne_internal (v : C.Vertex) (w : H.Internal) :
    host C hole H v ≠ .internal (.inr w) := by cases v <;> simp [host, Port.map]

theorem insert_source_injective {a b : H.Vertex}
    (ha : ¬ a.IsOutput) (hb : ¬ b.IsOutput)
    (eq : insert C hole H a = insert C hole H b) : a = b := by
  cases a with
  | output i => exact False.elim (ha trivial)
  | internal v =>
      cases b with
      | output i => exact False.elim (hb trivial)
      | internal w => simpa [insert] using eq
      | input j => exact False.elim (host_ne_internal C hole H _ _ eq.symm)
  | input i =>
      cases b with
      | output j => exact False.elim (hb trivial)
      | internal w => exact False.elim (host_ne_internal C hole H _ _ eq)
      | input j =>
          exact congrArg Port.input (C.sourcePort_injective hole (host_injective C hole H eq))

theorem insert_target_injective {a b : H.Vertex}
    (ha : ¬ a.IsInput) (hb : ¬ b.IsInput)
    (eq : insert C hole H a = insert C hole H b) : a = b := by
  cases a with
  | input i => exact False.elim (ha trivial)
  | internal v =>
      cases b with
      | input i => exact False.elim (hb trivial)
      | internal w => simpa [insert] using eq
      | output j => exact False.elim (host_ne_internal C hole H _ _ eq.symm)
  | output i =>
      cases b with
      | input j => exact False.elim (hb trivial)
      | internal w => exact False.elim (host_ne_internal C hole H _ _ eq)
      | output j =>
          exact congrArg Port.output (C.targetPort_injective hole (host_injective C hole H eq))

theorem insert_source_host {a : H.Vertex} {v : C.Vertex}
    (ha : ¬ a.IsOutput) (eq : insert C hole H a = host C hole H v) :
    ∃ i, a = .input i ∧ C.sourcePort hole i = v := by
  cases a with
  | output i => exact False.elim (ha trivial)
  | internal w => exact False.elim (host_ne_internal C hole H _ _ eq.symm)
  | input i => exact ⟨i, rfl, host_injective C hole H eq⟩

theorem insert_target_host {a : H.Vertex} {v : C.Vertex}
    (ha : ¬ a.IsInput) (eq : insert C hole H a = host C hole H v) :
    ∃ i, a = .output i ∧ C.targetPort hole i = v := by
  cases a with
  | input i => exact False.elim (ha trivial)
  | internal w => exact False.elim (host_ne_internal C hole H _ _ eq.symm)
  | output i => exact ⟨i, rfl, host_injective C hole H eq⟩

def source : Edge C hole H → List (Vertex C hole H)
  | .inl e => (C.source e.val).map (host C hole H)
  | .inr e => (H.source e).map (insert C hole H)

def target : Edge C hole H → List (Vertex C hole H)
  | .inl e => (C.target e.val).map (host C hole H)
  | .inr e => (H.target e).map (insert C hole H)

theorem source_nodup (e : Edge C hole H) : (source C hole H e).Nodup := by
  cases e with
  | inl e => exact nodup_map_on (C.source_nodup e.val) (fun _ _ _ _ h => host_injective C hole H h)
  | inr e =>
      exact nodup_map_on (H.source_nodup e) (fun _ ha _ hb h =>
        insert_source_injective C hole H (H.source_not_output ha) (H.source_not_output hb) h)

theorem target_nodup (e : Edge C hole H) : (target C hole H e).Nodup := by
  cases e with
  | inl e => exact nodup_map_on (C.target_nodup e.val) (fun _ _ _ _ h => host_injective C hole H h)
  | inr e =>
      exact nodup_map_on (H.target_nodup e) (fun _ ha _ hb h =>
        insert_target_injective C hole H (H.target_not_input ha) (H.target_not_input hb) h)

theorem source_unique {v : Vertex C hole H} {e f : Edge C hole H}
    (he : v ∈ source C hole H e) (hf : v ∈ source C hole H f) : e = f := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := host_injective C hole H eq
          subst b
          exact congrArg Sum.inl (Subtype.ext (C.source_unique ha hb))
      | inr f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          obtain ⟨i, _, hi⟩ := insert_source_host C hole H (H.source_not_output hb) eq
          have ah : a ∈ C.source hole := hi ▸ C.sourcePort_mem hole i
          exact False.elim (e.property (C.source_unique ha ah))
  | inr e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          obtain ⟨i, _, hi⟩ := insert_source_host C hole H (H.source_not_output ha) eq.symm
          have bh : b ∈ C.source hole := hi ▸ C.sourcePort_mem hole i
          exact False.elim (f.property (C.source_unique hb bh))
      | inr f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := insert_source_injective C hole H
            (H.source_not_output hb) (H.source_not_output ha) eq
          subst b
          exact congrArg Sum.inr (H.source_unique ha hb)

theorem target_unique {v : Vertex C hole H} {e f : Edge C hole H}
    (he : v ∈ target C hole H e) (hf : v ∈ target C hole H f) : e = f := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := host_injective C hole H eq
          subst b
          exact congrArg Sum.inl (Subtype.ext (C.target_unique ha hb))
      | inr f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          obtain ⟨i, _, hi⟩ := insert_target_host C hole H (H.target_not_input hb) eq
          have ah : a ∈ C.target hole := hi ▸ C.targetPort_mem hole i
          exact False.elim (e.property (C.target_unique ha ah))
  | inr e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          obtain ⟨i, _, hi⟩ := insert_target_host C hole H (H.target_not_input ha) eq.symm
          have bh : b ∈ C.target hole := hi ▸ C.targetPort_mem hole i
          exact False.elim (f.property (C.target_unique hb bh))
      | inr f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := insert_target_injective C hole H
            (H.target_not_input hb) (H.target_not_input ha) eq
          subst b
          exact congrArg Sum.inr (H.target_unique ha hb)

theorem source_not_output {e : Edge C hole H} {v : Vertex C hole H}
    (h : v ∈ source C hole H e) : ¬ v.IsOutput := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      simpa [host] using C.source_not_output ha
  | inr e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      cases a with
      | internal w => simp [insert, Port.IsOutput]
      | input i => simpa [insert, host] using C.source_not_output (C.sourcePort_mem hole i)
      | output i => exact False.elim (H.source_not_output ha trivial)

theorem target_not_input {e : Edge C hole H} {v : Vertex C hole H}
    (h : v ∈ target C hole H e) : ¬ v.IsInput := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      simpa [host] using C.target_not_input ha
  | inr e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      cases a with
      | internal w => simp [insert, Port.IsInput]
      | output i => simpa [insert, host] using C.target_not_input (C.targetPort_mem hole i)
      | input i => exact False.elim (H.target_not_input ha trivial)

theorem source_host_covered (v : C.Vertex) (hv : ¬ v.IsOutput) :
    ∃ e, host C hole H v ∈ source C hole H e := by
  classical
  obtain ⟨e, he⟩ := (C.source_coverage v).mpr hv
  by_cases eq : e = hole
  · subst e
    obtain ⟨i, rfl⟩ := (C.mem_source_iff_port hole v).mp he
    obtain ⟨f, hf⟩ := (H.source_coverage (.input i)).mpr (by simp [Port.IsOutput])
    exact ⟨.inr f, List.mem_map.mpr ⟨.input i, hf, rfl⟩⟩
  · exact ⟨.inl ⟨e, eq⟩, List.mem_map.mpr ⟨v, he, rfl⟩⟩

theorem target_host_covered (v : C.Vertex) (hv : ¬ v.IsInput) :
    ∃ e, host C hole H v ∈ target C hole H e := by
  classical
  obtain ⟨e, he⟩ := (C.target_coverage v).mpr hv
  by_cases eq : e = hole
  · subst e
    obtain ⟨i, rfl⟩ := (C.mem_target_iff_port hole v).mp he
    obtain ⟨f, hf⟩ := (H.target_coverage (.output i)).mpr (by simp [Port.IsInput])
    exact ⟨.inr f, List.mem_map.mpr ⟨.output i, hf, rfl⟩⟩
  · exact ⟨.inl ⟨e, eq⟩, List.mem_map.mpr ⟨v, he, rfl⟩⟩

theorem source_coverage (v : Vertex C hole H) :
    (∃ e, v ∈ source C hole H e) ↔ ¬ v.IsOutput := by
  constructor
  · rintro ⟨e, h⟩
    exact source_not_output C hole H h
  · intro hv
    cases v with
    | internal x =>
        cases x with
        | inl x => exact source_host_covered C hole H (.internal x) hv
        | inr x =>
            obtain ⟨e, he⟩ := (H.source_coverage (.internal x)).mpr (by simp [Port.IsOutput])
            exact ⟨.inr e, List.mem_map.mpr ⟨.internal x, he, rfl⟩⟩
    | input i => exact source_host_covered C hole H (.input i) hv
    | output i => exact False.elim (hv trivial)

theorem target_coverage (v : Vertex C hole H) :
    (∃ e, v ∈ target C hole H e) ↔ ¬ v.IsInput := by
  constructor
  · rintro ⟨e, h⟩
    exact target_not_input C hole H h
  · intro hv
    cases v with
    | internal x =>
        cases x with
        | inl x => exact target_host_covered C hole H (.internal x) hv
        | inr x =>
            obtain ⟨e, he⟩ := (H.target_coverage (.internal x)).mpr (by simp [Port.IsInput])
            exact ⟨.inr e, List.mem_map.mpr ⟨.internal x, he, rfl⟩⟩
    | output i => exact target_host_covered C hole H (.output i) hv
    | input i => exact False.elim (hv trivial)

def internalLabel : C.Internal ⊕ H.Internal → L := Sum.elim C.internalLabel H.internalLabel

def edgeLabel : Edge C hole H → Op
  | .inl e => C.edgeLabel e.val
  | .inr e => H.edgeLabel e

theorem host_label (v : C.Vertex) :
    Port.label (internalLabel C hole H) (host C hole H v) = C.vertexLabel v := by
  cases v <;> rfl

theorem insert_label (v : H.Vertex) :
    Port.label (internalLabel C hole H) (insert C hole H v) = H.vertexLabel v := by
  cases v with
  | internal w => rfl
  | input i => exact (host_label C hole H _).trans (C.sourcePort_label hole i)
  | output i => exact (host_label C hole H _).trans (C.targetPort_label hole i)

theorem source_typed (e : Edge C hole H) :
    (source C hole H e).map (Port.label (internalLabel C hole H)) = σ.input (edgeLabel C hole H e) := by
  cases e with
  | inl e =>
      simp only [source, List.map_map, edgeLabel]
      have eq : (Port.label (internalLabel C hole H) ∘ host C hole H) = C.vertexLabel := funext (host_label C hole H)
      rw [eq]; exact C.source_typed e.val
  | inr e =>
      simp only [source, List.map_map, edgeLabel]
      have eq : (Port.label (internalLabel C hole H) ∘ insert C hole H) = H.vertexLabel := funext (insert_label C hole H)
      rw [eq]; exact H.source_typed e

theorem target_typed (e : Edge C hole H) :
    (target C hole H e).map (Port.label (internalLabel C hole H)) = σ.output (edgeLabel C hole H e) := by
  cases e with
  | inl e =>
      simp only [target, List.map_map, edgeLabel]
      have eq : (Port.label (internalLabel C hole H) ∘ host C hole H) = C.vertexLabel := funext (host_label C hole H)
      rw [eq]; exact C.target_typed e.val
  | inr e =>
      simp only [target, List.map_map, edgeLabel]
      have eq : (Port.label (internalLabel C hole H) ∘ insert C hole H) = H.vertexLabel := funext (insert_label C hole H)
      rw [eq]; exact H.target_typed e

end Replacement

/-- Shallow, type-correct plugging preserves all finite hypergraph invariants
and the entire ordered external interface, including for self-loop holes. -/
@[reducible] noncomputable def plug {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O) (hole : C.Edge)
    (H : Net σ (σ.input (C.edgeLabel hole)) (σ.output (C.edgeLabel hole))) : Net σ I O where
  Internal := C.Internal ⊕ H.Internal
  Edge := Replacement.Edge C hole H
  finiteInternal := C.finiteInternal.sum H.finiteInternal
  finiteEdge := (C.finiteEdge.subtype (· ≠ hole)).sum H.finiteEdge
  internalLabel := Replacement.internalLabel C hole H
  edgeLabel := Replacement.edgeLabel C hole H
  source := Replacement.source C hole H
  target := Replacement.target C hole H
  source_nodup := Replacement.source_nodup C hole H
  target_nodup := Replacement.target_nodup C hole H
  source_unique := Replacement.source_unique C hole H
  target_unique := Replacement.target_unique C hole H
  source_coverage := Replacement.source_coverage C hole H
  target_coverage := Replacement.target_coverage C hole H
  source_typed := Replacement.source_typed C hole H
  target_typed := Replacement.target_typed C hole H

end Hypernets.Graph.Net
