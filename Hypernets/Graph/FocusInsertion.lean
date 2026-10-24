import Hypernets.Graph.Search

/-! Explicit focus insertion by splitting a non-output term vertex (§6.2).
The old vertex is the focus source; a fresh internal vertex is its target. -/
namespace Hypernets.Linear.FocusInsertion
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (G : Hypernet ops d I O)

abbrev Vertex := Port (G.Internal ⊕ Fin 1) I.length O.length

def host : G.Vertex → Vertex G := Port.map Sum.inl

def fresh : Vertex G := .internal (.inr 0)

def collapse (v : G.Vertex) : Vertex G → G.Vertex
  | .internal (.inl x) => .internal x
  | .internal (.inr _) => v
  | .input i => .input i
  | .output i => .output i

theorem collapse_host (v w : G.Vertex) : collapse G v (host G w) = w := by cases w <;> rfl

theorem host_ne_fresh (w : G.Vertex) : host G w ≠ fresh G := by cases w <;> simp [host, fresh, Port.map]

theorem host_injective {v w : G.Vertex} (h : host G v = host G w) : v = w :=
  Port.map_injective (fun _ _ h => Sum.inl.inj h) h

/-- Redirect only source occurrences of the chosen vertex to the fresh vertex. -/
noncomputable def split (v w : G.Vertex) : Vertex G := by
  classical
  exact if w = v then fresh G else host G w

theorem collapse_split (v w : G.Vertex) : collapse G v (split G v w) = w := by
  classical
  by_cases h : w = v
  · subst w; simp [split, collapse, fresh]
  · simp [split, h, collapse_host]

theorem split_injective (v : G.Vertex) {a b : G.Vertex} (h : split G v a = split G v b) : a = b := by
  have eq := congrArg (collapse G v) h
  simpa only [collapse_split] using eq

theorem split_ne_host (v w : G.Vertex) : split G v w ≠ host G v := by
  classical
  by_cases h : w = v
  · subst w; simpa [split] using (host_ne_fresh G v).symm
  · simp only [split, ite_eq_right h]
    exact fun eq => h (host_injective G eq)

theorem vertex_cases (x : Vertex G) : (∃ w, x = host G w) ∨ x = fresh G := by
  cases x with
  | input i => exact Or.inl ⟨.input i, rfl⟩
  | output i => exact Or.inl ⟨.output i, rfl⟩
  | internal x =>
      cases x with
      | inl w => exact Or.inl ⟨.internal w, rfl⟩
      | inr i =>
          have eq : i = 0 := Fin.ext (by omega)
          subst i
          exact Or.inr rfl

def internalLabel : G.Internal ⊕ Fin 1 → Wire
  | .inl x => G.internalLabel x
  | .inr _ => .term

theorem host_label (w : G.Vertex) : Port.label (I := I) (O := O) (internalLabel G) (host G w) = G.vertexLabel w := by
  cases w <;> rfl

theorem split_label (v : G.Vertex) (term : G.vertexLabel v = .term) (w : G.Vertex) :
    Port.label (I := I) (O := O) (internalLabel G) (split G v w) = G.vertexLabel w := by
  classical
  by_cases h : w = v
  · subst w; simpa [split, fresh, Port.label, internalLabel] using term.symm
  · simp [split, h, host_label]

noncomputable def source (v : G.Vertex) : G.Edge ⊕ Fin 1 → List (Vertex G)
  | .inl e => (G.source e).map (split G v)
  | .inr _ => [host G v]

def target : G.Edge ⊕ Fin 1 → List (Vertex G)
  | .inl e => (G.target e).map (host G)
  | .inr _ => [fresh G]

theorem source_unique (v : G.Vertex) {x : Vertex G} {e f : G.Edge ⊕ Fin 1}
    (he : x ∈ source G v e) (hf : x ∈ source G v f) : e = f := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := split_injective G v eq
          subst b
          exact congrArg Sum.inl (G.source_unique ha hb)
      | inr i => exact False.elim (split_ne_host G v a (List.mem_singleton.mp hf))
  | inr i =>
      have hx := List.mem_singleton.mp he
      subst x
      cases f with
      | inl f =>
          obtain ⟨a, _, eq⟩ := List.mem_map.mp hf
          exact False.elim (split_ne_host G v a eq)
      | inr j => congr 1; apply Fin.ext; omega

theorem target_unique {x : Vertex G} {e f : G.Edge ⊕ Fin 1}
    (he : x ∈ target G e) (hf : x ∈ target G f) : e = f := by
  cases e with
  | inl e =>
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      cases f with
      | inl f =>
          obtain ⟨b, hb, eq⟩ := List.mem_map.mp hf
          have ab := host_injective G eq
          subst b
          exact congrArg Sum.inl (G.target_unique ha hb)
      | inr i => exact False.elim (host_ne_fresh G a (List.mem_singleton.mp hf))
  | inr i =>
      have hx := List.mem_singleton.mp he
      subst x
      cases f with
      | inl f =>
          obtain ⟨a, _, eq⟩ := List.mem_map.mp hf
          exact False.elim (host_ne_fresh G a eq)
      | inr j => congr 1; apply Fin.ext; omega

theorem source_coverage (v : G.Vertex) (notOutput : ¬ v.IsOutput) (x : Vertex G) :
    (∃ e, x ∈ source G v e) ↔ ¬ x.IsOutput := by
  classical
  constructor
  · rintro ⟨e, he⟩
    cases e with
    | inl e =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
        by_cases h : w = v
        · simp [split, h, fresh, Port.IsOutput]
        · simpa [split, h, host] using G.source_not_output hw
    | inr i =>
        have eq := List.mem_singleton.mp he
        subst x
        simpa [host] using notOutput
  · intro hx
    cases vertex_cases G x with
    | inl old =>
        obtain ⟨w, rfl⟩ := old
        by_cases h : w = v
        · subst w; exact ⟨.inr 0, by simp [source]⟩
        · have hw : ¬ w.IsOutput := by simpa [host] using hx
          obtain ⟨e, he⟩ := (G.source_coverage w).mpr hw
          exact ⟨.inl e, List.mem_map.mpr ⟨w, he, by simp [split, h]⟩⟩
    | inr eq =>
        subst x
        obtain ⟨e, he⟩ := (G.source_coverage v).mpr notOutput
        exact ⟨.inl e, List.mem_map.mpr ⟨v, he, by simp [split]⟩⟩

theorem target_coverage (x : Vertex G) : (∃ e, x ∈ target G e) ↔ ¬ x.IsInput := by
  constructor
  · rintro ⟨e, he⟩
    cases e with
    | inl e =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
        simpa [host] using G.target_not_input hw
    | inr i =>
        have eq := List.mem_singleton.mp he
        subst x
        simp [fresh, Port.IsInput]
  · intro hx
    cases vertex_cases G x with
    | inl old =>
        obtain ⟨w, rfl⟩ := old
        have hw : ¬ w.IsInput := by simpa [host] using hx
        obtain ⟨e, he⟩ := (G.target_coverage w).mpr hw
        exact ⟨.inl e, List.mem_map.mpr ⟨w, he, rfl⟩⟩
    | inr eq => subst x; exact ⟨.inr 0, by simp [target]⟩

/-- Insert an actual focus edge, proving all finite typed-net invariants. -/
noncomputable def insert (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) : Hypernet ops d I O where
  Internal := G.Internal ⊕ Fin 1
  Edge := G.Edge ⊕ Fin 1
  finiteInternal := G.finiteInternal.sum (Enumeration.fin 1)
  finiteEdge := G.finiteEdge.sum (Enumeration.fin 1)
  internalLabel := internalLabel G
  edgeLabel := fun e => match e with | .inl e => G.edgeLabel e | .inr _ => focusLabel ops d mode
  source := source G v
  target := target G
  source_nodup := by
    intro e
    cases e with
    | inl e => exact nodup_map_on (G.source_nodup e) (fun _ _ _ _ eq => split_injective G v eq)
    | inr _ => simp [source]
  target_nodup := by
    intro e
    cases e with
    | inl e => exact nodup_map_on (G.target_nodup e) (fun _ _ _ _ eq => host_injective G eq)
    | inr _ => simp [target]
  source_unique := source_unique G v
  target_unique := target_unique G
  source_coverage := source_coverage G v notOutput
  target_coverage := target_coverage G
  source_typed := by
    intro e
    cases e with
    | inl e =>
        change ((G.source e).map (split G v)).map _ = _
        rw [List.map_map]
        have eq : (fun w => Port.label (I := I) (O := O) (internalLabel G) (split G v w)) = G.vertexLabel :=
          funext (split_label G v term)
        change (G.source e).map (fun w => Port.label (internalLabel G) (split G v w)) = _
        rw [eq]
        exact G.source_typed e
    | inr i =>
        change [Port.label (internalLabel G) (host G v)] = _
        rw [host_label, term]
        cases d <;> rfl
  target_typed := by
    intro e
    cases e with
    | inl e =>
        change ((G.target e).map (host G)).map _ = _
        rw [List.map_map]
        have eq : (fun w => Port.label (I := I) (O := O) (internalLabel G) (host G w)) = G.vertexLabel := funext (host_label G)
        change (G.target e).map (fun w => Port.label (internalLabel G) (host G w)) = _
        rw [eq]
        exact G.target_typed e
    | inr i => cases d <;> rfl

/-- Inserting into a globally focus-free graph gives a globally unique focus. -/
noncomputable def focussed (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (free : FocusFree G) :
    Focussed (insert G v term notOutput mode) where
  edge := .inr 0
  mode := mode
  label := rfl
  other_free := by
    intro e ne
    cases e with
    | inl e => exact free e
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  source := host G v
  target := fresh G
  source_eq := rfl
  target_eq := rfl
  self_acyclic := host_ne_fresh G v
  not_exposed := by simp [fresh, Port.IsOutput]

/-- Contracting the inserted focus recovers every original source list. -/
theorem collapse_sources (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (e : G.Edge) :
    ((insert G v term notOutput mode).source (.inl e)).map (collapse G v) = G.source e := by
  change ((G.source e).map (split G v)).map _ = _
  simp only [List.map_map]
  have eq : (fun w => collapse G v (split G v w)) = id := funext (collapse_split G v)
  change (G.source e).map (fun w => collapse G v (split G v w)) = _
  rw [eq, List.map_id]

theorem collapse_targets (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (e : G.Edge) :
    ((insert G v term notOutput mode).target (.inl e)).map (collapse G v) = G.target e := by
  change ((G.target e).map (host G)).map _ = _
  simp only [List.map_map]
  have eq : (fun w => collapse G v (host G w)) = id := funext (collapse_host G v)
  change (G.target e).map (fun w => collapse G v (host G w)) = _
  rw [eq, List.map_id]

/-- Focus insertion introduces no holes, including inside boxes. -/
theorem holeFree (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (free : HoleFree G) :
    HoleFree (insert G v term notOutput mode) := by
  intro h present
  obtain ⟨⟨e, pos⟩, hp⟩ := (hasHole_iff_occurrences _ h).mp present
  cases e with
  | inl e =>
      apply free h
      apply (hasHole_iff_occurrences G h).mpr
      exact ⟨⟨e, pos⟩, hp⟩
  | inr i =>
      cases d with
      | zero =>
          cases pos with
          | inl u => cases hp
          | inr impossible => exact nomatch impossible
      | succ d =>
          cases pos with
          | inl u => cases hp
          | inr impossible => exact nomatch impossible

/-- Input status of the explicit focus source agrees with the coordinate. -/
theorem boundary_iff (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (free : FocusFree G) :
    ((focussed G v term notOutput mode free).Initial ↔ mode = .search ∧ v.IsInput) ∧
    ((focussed G v term notOutput mode free).Final ↔ mode = .backtrack ∧ v.IsInput) := by
  cases v <;> exact ⟨Iff.rfl, Iff.rfl⟩

end Hypernets.Linear.FocusInsertion
