import Hypernets.Graph.Plugging

/-! Paths and the preservation/reflection statements at the end of Appendix B. -/

namespace Hypernets.Graph.Net

universe u

variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

def Adjacent (G : Net σ I O) (e f : G.Edge) : Prop :=
  ∃ v, v ∈ G.target e ∧ v ∈ G.source f

/-- Nonempty edge paths, permitting repeated edges as in the paper. -/
inductive Path (G : Net σ I O) : List G.Edge → Prop where
  | single (e) : Path G [e]
  | cons {e f es} : G.Adjacent e f → Path G (f :: es) → Path G (e :: f :: es)

theorem path_pair_iff {G : Net σ I O} {e f : G.Edge} {es} :
    G.Path (e :: f :: es) ↔ G.Adjacent e f ∧ G.Path (f :: es) := by
  constructor
  · intro h; cases h with | cons a p => exact ⟨a, p⟩
  · rintro ⟨a, p⟩; exact .cons a p

theorem Path.map {Op' : Type u} {τ : Signature L Op'} {J K : List L}
    {G : Net σ I O} {H : Net τ J K} (f : G.Edge → H.Edge)
    (preserve : ∀ {e e'}, G.Adjacent e e' → H.Adjacent (f e) (f e'))
    {es} (h : G.Path es) : H.Path (es.map f) := by
  induction h with
  | single e => exact .single _
  | cons adjacent _ ih => exact .cons (preserve adjacent) ih

theorem path_map_iff {Op' : Type u} {τ : Signature L Op'} {J K : List L}
    {G : Net σ I O} {H : Net τ J K} (f : G.Edge → H.Edge)
    (adj : ∀ e e', H.Adjacent (f e) (f e') ↔ G.Adjacent e e') (es) :
    H.Path (es.map f) ↔ G.Path es := by
  induction es with
  | nil => constructor <;> intro h <;> cases h
  | cons e es ih =>
      cases es with
      | nil => exact ⟨fun _ => .single _, fun _ => .single _⟩
      | cons e' es => simpa [path_pair_iff, adj] using (and_congr (adj e e') ih)

namespace Replacement

variable (C : Net σ I O) (hole : C.Edge)
    (H : Net σ (σ.input (C.edgeLabel hole)) (σ.output (C.edgeLabel hole)))

/-- A path consisting only of surviving context edges sees precisely its old
adjacencies. This does not require that the replaced hole be non-self-looping. -/
theorem adjacent_host_iff (e f : {e : C.Edge // e ≠ hole}) :
    (C.plug hole H).Adjacent (.inl e) (.inl f) ↔ C.Adjacent e.val f.val := by
  constructor
  · rintro ⟨v, hv, hw⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hw
    have ab := host_injective C hole H eq
    subst b
    exact ⟨a, ha, hb⟩
  · rintro ⟨v, hv, hw⟩
    exact ⟨host C hole H v, List.mem_map_of_mem hv, List.mem_map_of_mem hw⟩

theorem adjacent_insert (e f : H.Edge) (h : H.Adjacent e f) :
    (C.plug hole H).Adjacent (.inr e) (.inr f) := by
  obtain ⟨v, hv, hw⟩ := h
  exact ⟨insert C hole H v, List.mem_map_of_mem hv, List.mem_map_of_mem hw⟩

/-- The source and target lists of a non-self-looping hole are disjoint.
Individual source and target distinctness is already guaranteed by `Net`. -/
def NonSelfLoop : Prop := ∀ v, v ∈ C.source hole → v ∈ C.target hole → False

theorem insert_injective (noLoop : NonSelfLoop C hole) {a b : H.Vertex}
    (eq : insert C hole H a = insert C hole H b) : a = b := by
  cases a with
  | internal v =>
      cases b with
      | internal w => simpa [insert] using eq
      | input j => exact False.elim (host_ne_internal C hole H _ _ eq.symm)
      | output j => exact False.elim (host_ne_internal C hole H _ _ eq.symm)
  | input i =>
      cases b with
      | internal w => exact False.elim (host_ne_internal C hole H _ _ eq)
      | input j => exact congrArg Port.input (C.sourcePort_injective hole (host_injective C hole H eq))
      | output j =>
          have same := host_injective C hole H eq
          exact False.elim (noLoop _ (C.sourcePort_mem hole i) (same.symm ▸ C.targetPort_mem hole j))
  | output i =>
      cases b with
      | internal w => exact False.elim (host_ne_internal C hole H _ _ eq)
      | output j => exact congrArg Port.output (C.targetPort_injective hole (host_injective C hole H eq))
      | input j =>
          have same := host_injective C hole H eq
          exact False.elim (noLoop _ (C.sourcePort_mem hole j) (same ▸ C.targetPort_mem hole i))

theorem adjacent_insert_iff (noLoop : NonSelfLoop C hole) (e f : H.Edge) :
    (C.plug hole H).Adjacent (.inr e) (.inr f) ↔ H.Adjacent e f := by
  constructor
  · rintro ⟨v, hv, hw⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hw
    have ab := insert_injective C hole H noLoop eq
    subst b
    exact ⟨a, ha, hb⟩
  · exact adjacent_insert C hole H e f

/-- Surviving context paths are preserved and reflected, for arbitrary holes.
The source path is written on the surviving-edge subtype so avoidance of the
hole is checked by the type system rather than a separate side condition. -/
theorem path_host_iff (es : List {e : C.Edge // e ≠ hole}) :
    (C.plug hole H).Path (es.map Sum.inl) ↔ C.Path (es.map Subtype.val) := by
  induction es with
  | nil => constructor <;> intro h <;> cases h
  | cons e es ih =>
      cases es with
      | nil => exact ⟨fun _ => .single _, fun _ => .single _⟩
      | cons f es =>
          change (C.plug hole H).Path (.inl e :: .inl f :: es.map Sum.inl) ↔
            C.Path (e.val :: f.val :: es.map Subtype.val)
          rw [path_pair_iff (G := C.plug hole H), path_pair_iff (G := C)]
          exact and_congr (adjacent_host_iff C hole H e f) ih

theorem path_insert {es} (h : H.Path es) :
    (C.plug hole H).Path (es.map Sum.inr) :=
  Path.map (G := H) (H := C.plug hole H) (fun e => .inr e)
    (fun {e f} adj => adjacent_insert C hole H e f adj) h

/-- Reflection of inserted paths needs the precise extra condition noted in
Appendix B. We do not assert it unconditionally for self-loop holes. -/
theorem path_insert_iff (noLoop : NonSelfLoop C hole) (es : List H.Edge) :
    (C.plug hole H).Path (es.map Sum.inr) ↔ H.Path es :=
  path_map_iff (G := H) (H := C.plug hole H) (fun e => .inr e)
    (adjacent_insert_iff C hole H noLoop) es

end Replacement
end Hypernets.Graph.Net
