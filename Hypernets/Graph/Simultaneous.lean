import Hypernets.Graph.Constructors

/-! Simultaneous shallow expansion of every edge by a graph of its interface.
Unchanged edges can be supplied as corollas. All copies have disjoint internals. -/
namespace Hypernets.Graph.Net
universe u
namespace Expansion
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O)
    (H : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))

abbrev Internal := C.Internal ⊕ ((e : C.Edge) × (H e).Internal)
abbrev Vertex := Port (Internal C H) I.length O.length
abbrev Edge := (e : C.Edge) × (H e).Edge

def host : C.Vertex → Vertex C H := Port.map Sum.inl

def insert (e : C.Edge) : (H e).Vertex → Vertex C H
  | .internal v => .internal (.inr ⟨e, v⟩)
  | .input i => host C H (C.sourcePort e i)
  | .output i => host C H (C.targetPort e i)

theorem host_injective {a b : C.Vertex} (eq : host C H a = host C H b) : a = b :=
  Port.map_injective (fun _ _ h => Sum.inl.inj h) eq

theorem host_ne_internal (v : C.Vertex) (e : C.Edge) (w : (H e).Internal) :
    host C H v ≠ .internal (.inr ⟨e, w⟩) := by cases v <;> simp [host, Port.map]

theorem source_owner {e f : C.Edge} {a : (H e).Vertex} {b : (H f).Vertex}
    (ha : ¬ a.IsOutput) (hb : ¬ b.IsOutput) (eq : insert C H e a = insert C H f b) : e = f := by
  cases a with
  | output => exact False.elim (ha trivial)
  | internal x => cases b with
    | output => exact False.elim (hb trivial)
    | internal y => exact congrArg Sigma.fst (Sum.inr.inj (Port.internal.inj eq))
    | input j => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
  | input i => cases b with
    | output => exact False.elim (hb trivial)
    | internal y => exact False.elim (host_ne_internal C H _ _ _ eq)
    | input j =>
        have same := host_injective C H eq
        exact C.source_unique (C.sourcePort_mem e i) (same.symm ▸ C.sourcePort_mem f j)

theorem target_owner {e f : C.Edge} {a : (H e).Vertex} {b : (H f).Vertex}
    (ha : ¬ a.IsInput) (hb : ¬ b.IsInput) (eq : insert C H e a = insert C H f b) : e = f := by
  cases a with
  | input => exact False.elim (ha trivial)
  | internal x => cases b with
    | input => exact False.elim (hb trivial)
    | internal y => exact congrArg Sigma.fst (Sum.inr.inj (Port.internal.inj eq))
    | output j => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
  | output i => cases b with
    | input => exact False.elim (hb trivial)
    | internal y => exact False.elim (host_ne_internal C H _ _ _ eq)
    | output j =>
        have same := host_injective C H eq
        exact C.target_unique (C.targetPort_mem e i) (same.symm ▸ C.targetPort_mem f j)

theorem insert_source_injective (e : C.Edge) {a b : (H e).Vertex}
    (ha : ¬ a.IsOutput) (hb : ¬ b.IsOutput) (eq : insert C H e a = insert C H e b) : a = b := by
  cases a with
  | output => exact False.elim (ha trivial)
  | internal x => cases b with
    | output => exact False.elim (hb trivial)
    | internal y =>
        have h : (⟨e,x⟩ : (e : C.Edge) × (H e).Internal) = ⟨e,y⟩ := Sum.inr.inj (Port.internal.inj eq)
        exact congrArg Port.internal (eq_of_heq (Sigma.mk.inj h).2)
    | input j => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
  | input i => cases b with
    | output => exact False.elim (hb trivial)
    | internal y => exact False.elim (host_ne_internal C H _ _ _ eq)
    | input j => exact congrArg Port.input (C.sourcePort_injective e (host_injective C H eq))

theorem insert_target_injective (e : C.Edge) {a b : (H e).Vertex}
    (ha : ¬ a.IsInput) (hb : ¬ b.IsInput) (eq : insert C H e a = insert C H e b) : a = b := by
  cases a with
  | input => exact False.elim (ha trivial)
  | internal x => cases b with
    | input => exact False.elim (hb trivial)
    | internal y =>
        have h : (⟨e,x⟩ : (e : C.Edge) × (H e).Internal) = ⟨e,y⟩ := Sum.inr.inj (Port.internal.inj eq)
        exact congrArg Port.internal (eq_of_heq (Sigma.mk.inj h).2)
    | output j => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
  | output i => cases b with
    | input => exact False.elim (hb trivial)
    | internal y => exact False.elim (host_ne_internal C H _ _ _ eq)
    | output j => exact congrArg Port.output (C.targetPort_injective e (host_injective C H eq))

def source (e : Edge C H) := ((H e.1).source e.2).map (insert C H e.1)
def target (e : Edge C H) := ((H e.1).target e.2).map (insert C H e.1)

theorem source_nodup (e : Edge C H) : (source C H e).Nodup :=
  nodup_map_on ((H e.1).source_nodup e.2) (fun _ ha _ hb eq =>
    insert_source_injective C H e.1 ((H e.1).source_not_output ha) ((H e.1).source_not_output hb) eq)

theorem target_nodup (e : Edge C H) : (target C H e).Nodup :=
  nodup_map_on ((H e.1).target_nodup e.2) (fun _ ha _ hb eq =>
    insert_target_injective C H e.1 ((H e.1).target_not_input ha) ((H e.1).target_not_input hb) eq)

theorem source_unique {v : Vertex C H} {e f : Edge C H}
    (he : v ∈ source C H e) (hf : v ∈ source C H f) : e = f := by
  obtain ⟨e, x⟩ := e
  obtain ⟨f, y⟩ := f
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
  have same := source_owner C H ((H f).source_not_output hb) ((H e).source_not_output ha) eq
  subst f
  have ab := insert_source_injective C H e ((H e).source_not_output hb) ((H e).source_not_output ha) eq
  subst b
  exact congrArg (Sigma.mk e) ((H e).source_unique ha hb)

theorem target_unique {v : Vertex C H} {e f : Edge C H}
    (he : v ∈ target C H e) (hf : v ∈ target C H f) : e = f := by
  obtain ⟨e, x⟩ := e
  obtain ⟨f, y⟩ := f
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
  have same := target_owner C H ((H f).target_not_input hb) ((H e).target_not_input ha) eq
  subst f
  have ab := insert_target_injective C H e ((H e).target_not_input hb) ((H e).target_not_input ha) eq
  subst b
  exact congrArg (Sigma.mk e) ((H e).target_unique ha hb)

theorem source_not_output {e : Edge C H} {v : Vertex C H} (mem : v ∈ source C H e) : ¬ v.IsOutput := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp mem
  cases a with
  | internal => simp [insert, Port.IsOutput]
  | input i => simpa [insert, host] using C.source_not_output (C.sourcePort_mem e.1 i)
  | output => exact False.elim ((H e.1).source_not_output ha trivial)

theorem target_not_input {e : Edge C H} {v : Vertex C H} (mem : v ∈ target C H e) : ¬ v.IsInput := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp mem
  cases a with
  | internal => simp [insert, Port.IsInput]
  | output i => simpa [insert, host] using C.target_not_input (C.targetPort_mem e.1 i)
  | input => exact False.elim ((H e.1).target_not_input ha trivial)

theorem source_host_covered (v : C.Vertex) (notOutput : ¬ v.IsOutput) :
    ∃ e, host C H v ∈ source C H e := by
  obtain ⟨e, he⟩ := (C.source_coverage v).mpr notOutput
  obtain ⟨i, rfl⟩ := (C.mem_source_iff_port e v).mp he
  obtain ⟨f, hf⟩ := ((H e).source_coverage (.input i)).mpr (by simp [Port.IsOutput])
  exact ⟨⟨e,f⟩, List.mem_map_of_mem hf⟩

theorem target_host_covered (v : C.Vertex) (notInput : ¬ v.IsInput) :
    ∃ e, host C H v ∈ target C H e := by
  obtain ⟨e, he⟩ := (C.target_coverage v).mpr notInput
  obtain ⟨i, rfl⟩ := (C.mem_target_iff_port e v).mp he
  obtain ⟨f, hf⟩ := ((H e).target_coverage (.output i)).mpr (by simp [Port.IsInput])
  exact ⟨⟨e,f⟩, List.mem_map_of_mem hf⟩

theorem source_coverage (v : Vertex C H) : (∃ e, v ∈ source C H e) ↔ ¬ v.IsOutput := by
  constructor
  · rintro ⟨e, mem⟩; exact source_not_output C H mem
  · intro notOutput
    cases v with
    | internal v => cases v with
      | inl v => exact source_host_covered C H (.internal v) notOutput
      | inr v =>
          obtain ⟨e, he⟩ := ((H v.1).source_coverage (.internal v.2)).mpr (by simp [Port.IsOutput])
          exact ⟨⟨v.1,e⟩, List.mem_map_of_mem he⟩
    | input i => exact source_host_covered C H (.input i) notOutput
    | output => exact False.elim (notOutput trivial)

theorem target_coverage (v : Vertex C H) : (∃ e, v ∈ target C H e) ↔ ¬ v.IsInput := by
  constructor
  · rintro ⟨e, mem⟩; exact target_not_input C H mem
  · intro notInput
    cases v with
    | internal v => cases v with
      | inl v => exact target_host_covered C H (.internal v) notInput
      | inr v =>
          obtain ⟨e, he⟩ := ((H v.1).target_coverage (.internal v.2)).mpr (by simp [Port.IsInput])
          exact ⟨⟨v.1,e⟩, List.mem_map_of_mem he⟩
    | output i => exact target_host_covered C H (.output i) notInput
    | input => exact False.elim (notInput trivial)

def internalLabel : Internal C H → L := Sum.elim C.internalLabel (fun x => (H x.1).internalLabel x.2)
def edgeLabel (e : Edge C H) : Op := (H e.1).edgeLabel e.2

theorem host_label (v : C.Vertex) :
    Port.label (internalLabel C H) (host C H v) = C.vertexLabel v := by cases v <;> rfl

theorem insert_label (e : C.Edge) (v : (H e).Vertex) :
    Port.label (internalLabel C H) (insert C H e v) = (H e).vertexLabel v := by
  cases v with
  | internal => rfl
  | input i => exact (host_label C H _).trans (C.sourcePort_label e i)
  | output i => exact (host_label C H _).trans (C.targetPort_label e i)

theorem source_typed (e : Edge C H) :
    (source C H e).map (Port.label (internalLabel C H)) = σ.input (edgeLabel C H e) := by
  simp only [source, List.map_map, edgeLabel]
  have eq : (Port.label (internalLabel C H) ∘ insert C H e.1) = (H e.1).vertexLabel :=
    funext (insert_label C H e.1)
  rw [eq]
  exact (H e.1).source_typed e.2

theorem target_typed (e : Edge C H) :
    (target C H e).map (Port.label (internalLabel C H)) = σ.output (edgeLabel C H e) := by
  simp only [target, List.map_map, edgeLabel]
  have eq : (Port.label (internalLabel C H) ∘ insert C H e.1) = (H e.1).vertexLabel :=
    funext (insert_label C H e.1)
  rw [eq]
  exact (H e.1).target_typed e.2

end Expansion

/-- Finite simultaneous substitution with all incidence and typing laws proved.
An identity expansion uses the corolla of each original edge label. -/
@[reducible] def expand {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O)
    (H : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e))) : Net σ I O where
  Internal := Expansion.Internal C H
  Edge := Expansion.Edge C H
  finiteInternal := C.finiteInternal.sum (C.finiteEdge.sigma (fun e => (H e).finiteInternal))
  finiteEdge := C.finiteEdge.sigma (fun e => (H e).finiteEdge)
  internalLabel := Expansion.internalLabel C H
  edgeLabel := Expansion.edgeLabel C H
  source := Expansion.source C H
  target := Expansion.target C H
  source_nodup := Expansion.source_nodup C H
  target_nodup := Expansion.target_nodup C H
  source_unique := Expansion.source_unique C H
  target_unique := Expansion.target_unique C H
  source_coverage := Expansion.source_coverage C H
  target_coverage := Expansion.target_coverage C H
  source_typed := Expansion.source_typed C H
  target_typed := Expansion.target_typed C H

end Hypernets.Graph.Net
