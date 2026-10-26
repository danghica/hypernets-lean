import Hypernets.Copying.ArithmeticReductionRenaming

/-! Arithmetic deletion commutes with arbitrary typed shallow attachment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph
namespace Reduction
variable {d I O} (C : Hypernet d I O) (hole : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))}
    {head : G.Edge} {result : Nat}

theorem inserted_internal (x : G.Internal) {v : G.Vertex}
    (eq : Net.Replacement.insert C hole G v = .internal (.inr x)) : v = .internal x := by
  cases v with
  | internal y => exact congrArg Port.internal (Sum.inr.inj (Port.internal.inj eq))
  | input i => exact False.elim (Net.Replacement.host_ne_internal C hole G _ _ eq)
  | output i => exact False.elim (Net.Replacement.host_ne_internal C hole G _ _ eq)

theorem plug_target (closed : InternalTargets G head) (x) :
    Port.internal x ∈ (C.plug hole G).target (.inr head) ↔
      ∃ y, x = .inr y ∧ Port.internal y ∈ G.target head := by
  change _ ∈ (G.target head).map (Net.Replacement.insert C hole G) ↔ _
  constructor
  · intro h
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp h
    obtain ⟨y,rfl⟩ := closed v hv
    exact ⟨y,(Port.internal.inj eq).symm,hv⟩
  · rintro ⟨y,rfl,hy⟩; exact List.mem_map_of_mem hy

theorem plug_adjacent_host (closed : InternalTargets G head) (e : {e : C.Edge // e ≠ hole}) :
    ¬ (C.plug hole G).Adjacent (.inr head) (.inl e) := by
  rintro ⟨v,hv,hw⟩
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  obtain ⟨x,rfl⟩ := closed u hu
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp hw
  exact Net.Replacement.host_ne_internal C hole G w x eq

theorem plug_adjacent_inner (closed : InternalTargets G head) (e : G.Edge) :
    (C.plug hole G).Adjacent (.inr head) (.inr e) ↔ G.Adjacent head e := by
  constructor
  · rintro ⟨v,hv,hw⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    obtain ⟨x,rfl⟩ := closed u hu
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hw
    exact ⟨.internal x,hu,(inserted_internal C hole x eq) ▸ hw⟩
  · exact (MatchEmbedding.plug C hole G).adjacent

theorem plug_closed (closed : InternalTargets G head) : InternalTargets (C.plug hole G) (.inr head) := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  obtain ⟨x,rfl⟩ := closed w hw
  exact ⟨.inr x,rfl⟩

theorem plug_port (a : Reduction G H head result) (v : H.Vertex) :
    Port.map (Sum.map id a.vertices) (Net.Replacement.insert C hole H v) =
      Net.Replacement.insert C hole G (Port.map a.vertices v) := by
  cases v with
  | internal v => rfl
  | input i =>
    simp only [Net.Replacement.insert,Net.Replacement.host,Port.map]
    cases C.sourcePort hole i <;> rfl
  | output i =>
    simp only [Net.Replacement.insert,Net.Replacement.host,Port.map]
    cases C.targetPort hole i <;> rfl

theorem plug_host (a : Reduction G H head result) (v : C.Vertex) :
    Port.map (Sum.map id a.vertices) (Net.Replacement.host C hole H v) = Net.Replacement.host C hole G v := by
  cases v <;> rfl

/-- Host carriers survive unchanged; only the embedded internal operand occurrences disappear. -/
def plug (a : Reduction G H head result) (closed : InternalTargets G head) :
    Reduction (C.plug hole G) (C.plug hole H) (.inr head) result where
  vertices := Sum.map id a.vertices
  vertex_injective := by
    intro x y eq
    cases x <;> cases y <;> simp only [Sum.map] at eq
    · exact congrArg Sum.inl (Sum.inl.inj eq)
    · cases eq
    · cases eq
    · exact congrArg Sum.inr (a.vertex_injective (Sum.inr.inj eq))
  vertex_range x := by
    rw [plug_target C hole closed]
    cases x with
    | inl x =>
      constructor
      · rintro _ ⟨y,eq,_⟩; cases eq
      · intro _; exact ⟨.inl x,rfl⟩
    | inr x =>
      constructor
      · rintro ⟨y,hy⟩ ⟨z,eq,hz⟩
        have zx := Sum.inr.inj eq
        subst z
        cases y with
        | inl y => cases hy
        | inr y => exact (a.vertex_range x).mp ⟨y,Sum.inr.inj hy⟩ hz
      · intro hn
        have hx : Port.internal x ∉ G.target head := fun h => hn ⟨x,rfl,h⟩
        obtain ⟨y,hy⟩ := (a.vertex_range x).mpr hx
        exact ⟨.inr y,congrArg Sum.inr hy⟩
  edges := Sum.map id a.edges
  edge_injective := by
    intro x y eq
    cases x <;> cases y <;> simp only [Sum.map] at eq
    · exact congrArg Sum.inl (Sum.inl.inj eq)
    · cases eq
    · cases eq
    · exact congrArg Sum.inr (a.edge_injective (Sum.inr.inj eq))
  edge_range e := by
    cases e with
    | inl e => exact ⟨fun _ => plug_adjacent_host C hole closed e,fun _ => ⟨.inl e,rfl⟩⟩
    | inr e =>
      rw [plug_adjacent_inner C hole closed,← a.edge_range]
      constructor
      · rintro ⟨f,hf⟩
        cases f with
        | inl f => cases hf
        | inr f => exact ⟨f,Sum.inr.inj hf⟩
      · rintro ⟨f,hf⟩; exact ⟨.inr f,congrArg Sum.inr hf⟩
  internal_label x := by cases x with
    | inl x => rfl
    | inr x => exact a.internal_label x
  edge_head e eq := by
    cases e with
    | inl e => cases eq
    | inr e => exact a.edge_head e (Sum.inr.inj eq)
  edge_other e ne := by
    cases e with
    | inl e => exact labelEquiv_refl d _
    | inr e => exact a.edge_other e (fun eq => ne (congrArg Sum.inr eq))
  source e := by
    cases e with
    | inl e =>
      change ((C.source e.val).map (Net.Replacement.host C hole H)).map (Port.map (Sum.map id a.vertices)) = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => plug_host C hole a v)
    | inr e =>
      change ((H.source e).map (Net.Replacement.insert C hole H)).map (Port.map (Sum.map id a.vertices)) = _
      rw [List.map_map]
      calc
        _ = ((H.source e).map (Port.map a.vertices)).map (Net.Replacement.insert C hole G) := by
          rw [List.map_map]
          exact List.map_congr_left (fun v _ => plug_port C hole a v)
        _ = _ := by rw [a.source]; rfl
  target_head e eq := by
    cases e with
    | inl e => cases eq
    | inr e =>
      change (H.target e).map _ = []
      rw [a.target_head e (Sum.inr.inj eq)]; rfl
  target_other e ne := by
    cases e with
    | inl e =>
      change ((C.target e.val).map (Net.Replacement.host C hole H)).map (Port.map (Sum.map id a.vertices)) = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => plug_host C hole a v)
    | inr e =>
      change ((H.target e).map (Net.Replacement.insert C hole H)).map (Port.map (Sum.map id a.vertices)) = _
      rw [List.map_map]
      calc
        _ = ((H.target e).map (Port.map a.vertices)).map (Net.Replacement.insert C hole G) := by
          rw [List.map_map]
          exact List.map_congr_left (fun v _ => plug_port C hole a v)
        _ = _ := by rw [a.target_other e (fun eq => ne (congrArg Sum.inr eq))]; rfl
end Reduction
end Hypernets.Copying.Arithmetic
