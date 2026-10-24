import Hypernets.Graph.FocusInsertion

/-! Focus subdivision on the incoming side of a non-input port, including outputs. -/
namespace Hypernets.Linear.OutputFocusInsertion
open Graph FocusInsertion
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (G : Hypernet ops d I O)

noncomputable def target (v : G.Vertex) : G.Edge ⊕ Fin 1 → List (Vertex G)
  | .inl e => (G.target e).map (split G v)
  | .inr _ => [host G v]

def source : G.Edge ⊕ Fin 1 → List (Vertex G)
  | .inl e => (G.source e).map (host G)
  | .inr _ => [fresh G]

theorem target_unique (v : G.Vertex) {x : Vertex G} {e f : G.Edge ⊕ Fin 1}
    (he : x ∈ target G v e) (hf : x ∈ target G v f) : e = f := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := split_injective G v eq
          subst b
          exact congrArg Sum.inl (G.target_unique ha hb)
      | inr i => exact False.elim (split_ne_host G v a (List.mem_singleton.mp hf))
  | inr i =>
      have hx := List.mem_singleton.mp he
      subst x
      cases f with
      | inl f =>
          obtain ⟨a, _, eq⟩ := List.mem_map.mp hf
          exact False.elim (split_ne_host G v a eq)
      | inr j => congr 1; apply Fin.ext; omega

theorem source_unique {x : Vertex G} {e f : G.Edge ⊕ Fin 1}
    (he : x ∈ source G e) (hf : x ∈ source G f) : e = f := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := host_injective G eq
          subst b
          exact congrArg Sum.inl (G.source_unique ha hb)
      | inr i => exact False.elim (host_ne_fresh G a (List.mem_singleton.mp hf))
  | inr i =>
      have hx := List.mem_singleton.mp he
      subst x
      cases f with
      | inl f =>
          obtain ⟨a, _, eq⟩ := List.mem_map.mp hf
          exact False.elim (host_ne_fresh G a eq)
      | inr j => congr 1; apply Fin.ext; omega

theorem target_coverage (v : G.Vertex) (notInput : ¬ v.IsInput) (x : Vertex G) :
    (∃ e, x ∈ target G v e) ↔ ¬ x.IsInput := by
  classical
  constructor
  · rintro ⟨e, he⟩
    cases e with
    | inl e =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
        by_cases h : w = v
        · simp [split, h, fresh, Port.IsInput]
        · simpa [split, h, host] using G.target_not_input hw
    | inr i =>
        have eq := List.mem_singleton.mp he
        subst x
        simpa [host] using notInput
  · intro hx
    cases vertex_cases G x with
    | inl old =>
        obtain ⟨w, rfl⟩ := old
        by_cases h : w = v
        · subst w; exact ⟨.inr 0, by simp [target]⟩
        · have hw : ¬ w.IsInput := by simpa [host] using hx
          obtain ⟨e, he⟩ := (G.target_coverage w).mpr hw
          exact ⟨.inl e, List.mem_map.mpr ⟨w, he, by simp [split, h]⟩⟩
    | inr eq =>
        subst x
        obtain ⟨e, he⟩ := (G.target_coverage v).mpr notInput
        exact ⟨.inl e, List.mem_map.mpr ⟨v, he, by simp [split]⟩⟩

theorem source_coverage (x : Vertex G) : (∃ e, x ∈ source G e) ↔ ¬ x.IsOutput := by
  constructor
  · rintro ⟨e, he⟩
    cases e with
    | inl e =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
        simpa [host] using G.source_not_output hw
    | inr i =>
        have eq := List.mem_singleton.mp he
        subst x
        simp [fresh, Port.IsOutput]
  · intro hx
    cases vertex_cases G x with
    | inl old =>
        obtain ⟨w, rfl⟩ := old
        have hw : ¬ w.IsOutput := by simpa [host] using hx
        obtain ⟨e, he⟩ := (G.source_coverage w).mpr hw
        exact ⟨.inl e, List.mem_map.mpr ⟨w, he, rfl⟩⟩
    | inr eq => subst x; exact ⟨.inr 0, by simp [source]⟩

/-- Insert an actual focus edge, proving all finite typed-net invariants. -/
@[reducible] noncomputable def insert (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notInput : ¬ v.IsInput) (mode : Focus) : Hypernet ops d I O where
  Internal := G.Internal ⊕ Fin 1
  Edge := G.Edge ⊕ Fin 1
  finiteInternal := G.finiteInternal.sum (Enumeration.fin 1)
  finiteEdge := G.finiteEdge.sum (Enumeration.fin 1)
  internalLabel := internalLabel G
  edgeLabel := fun e => match e with | .inl e => G.edgeLabel e | .inr _ => focusLabel ops d mode
  target := target G v
  source := source G
  target_nodup := by
    intro e
    cases e with
    | inl e => exact nodup_map_on (G.target_nodup e) (fun _ _ _ _ eq => split_injective G v eq)
    | inr _ => simp [target]
  source_nodup := by
    intro e
    cases e with
    | inl e => exact nodup_map_on (G.source_nodup e) (fun _ _ _ _ eq => host_injective G eq)
    | inr _ => simp [source]
  target_unique := target_unique G v
  source_unique := source_unique G
  target_coverage := target_coverage G v notInput
  source_coverage := source_coverage G
  target_typed := by
    intro e
    cases e with
    | inl e =>
        change ((G.target e).map (split G v)).map _ = _
        rw [List.map_map]
        have eq : (fun w => Port.label (I := I) (O := O) (internalLabel G) (split G v w)) = G.vertexLabel :=
          funext (split_label G v term)
        change (G.target e).map (fun w => Port.label (internalLabel G) (split G v w)) = _
        rw [eq]
        exact G.target_typed e
    | inr i =>
        change [Port.label (internalLabel G) (host G v)] = _
        rw [host_label, term]
        cases d <;> rfl
  source_typed := by
    intro e
    cases e with
    | inl e =>
        change ((G.source e).map (host G)).map _ = _
        rw [List.map_map]
        have eq : (fun w => Port.label (I := I) (O := O) (internalLabel G) (host G w)) = G.vertexLabel := funext (host_label G)
        change (G.source e).map (fun w => Port.label (internalLabel G) (host G w)) = _
        rw [eq]
        exact G.source_typed e
    | inr i => cases d <;> rfl

/-- Inserting into a globally focus-free graph gives a globally unique focus. -/
@[reducible] noncomputable def focussed (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notInput : ¬ v.IsInput) (mode : Focus) (free : FocusFree G) :
    Focussed (insert G v term notInput mode) where
  edge := .inr 0
  mode := mode
  label := rfl
  other_free := by
    intro e ne
    cases e with
    | inl e => exact free e
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  target := host G v
  source := fresh G
  target_eq := rfl
  source_eq := rfl
  self_acyclic := (host_ne_fresh G v).symm
  not_exposed := by simp [fresh, Port.IsInput]


end Hypernets.Linear.OutputFocusInsertion
