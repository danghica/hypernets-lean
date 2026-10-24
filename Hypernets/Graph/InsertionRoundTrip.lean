import Hypernets.Graph.StateSearch

/-! The other round trip: inserting a focus and then erasing it recovers the
underlying graph and the chosen coordinate, up to literal-label isomorphism. -/
namespace Hypernets.Linear.FocusInsertion
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}

/-- Delete the fresh singleton summand, retaining precisely the old carrier. -/
def deleteFresh {A : Type} : Bijection {x : A ⊕ Fin 1 // x ≠ .inr 0} A where
  toFun := fun x => match x with
    | ⟨.inl a, _⟩ => a
    | ⟨.inr i, ne⟩ => False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  invFun := fun a => ⟨.inl a, by simp⟩
  left_inv := by
    intro x
    rcases x with ⟨x, ne⟩
    cases x with
    | inl a => rfl
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  right_inv := by intro a; rfl

variable (G : Hypernet ops d I []) (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (free : FocusFree G)

/-- Erase the distinguished fresh focus of an insertion. -/
noncomputable abbrev erasedInsertion : Hypernet ops d I [] :=
  FocusErasure.erase (focussed G v term notOutput mode free) (.inr 0) rfl

/-- On retained ports, deleting the singleton summand is the old collapse map. -/
theorem deleteFresh_port (x : (erasedInsertion G v term notOutput mode free).Vertex) :
    Port.map deleteFresh.toFun x = collapse G v (FocusErasure.lift (G := insert G v term notOutput mode) (.inr 0) x) := by
  cases x with
  | internal x =>
      rcases x with ⟨x, ne⟩
      cases x with
      | inl a => rfl
      | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  | input i => rfl
  | output i => exact Fin.elim0 i

/-- The joined vertex restores the original insertion position. -/
theorem erase_position :
    Port.map deleteFresh.toFun
      (FocusErasure.position (focussed G v term notOutput mode free) (.inr 0) rfl) = v := by
  erw [deleteFresh_port G v term notOutput mode free, FocusErasure.lift_position]
  exact collapse_host G v v

/-- General contraction followed by deleting the fresh names is ordinary collapse. -/
theorem erase_contract (w : (insert G v term notOutput mode).Vertex) :
    Port.map deleteFresh.toFun
      (FocusErasure.contract (focussed G v term notOutput mode free) (.inr 0) rfl w) =
      collapse G v w := by
  classical
  by_cases h : w = .internal (.inr 0)
  · subst w
    erw [FocusErasure.contract_target, erase_position]
    rfl
  · erw [deleteFresh_port G v term notOutput mode free, FocusErasure.lift_contract _ _ _ _ h]

/-- Insertion followed by general erasure restores all labels and ordered incidences. -/
noncomputable def erase_iso : Net.Iso (erasedInsertion G v term notOutput mode free) G where
  vertices := deleteFresh
  edges := deleteFresh
  internal_label := by
    rintro ⟨x, ne⟩
    cases x with
    | inl a => rfl
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  edge_label := by
    rintro ⟨e, ne⟩
    cases e with
    | inl e => rfl
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  source := by
    rintro ⟨e, ne⟩
    cases e with
    | inl e =>
        change (((G.source e).map (split G v)).map _).map _ = G.source e
        simp only [List.map_map]
        have point : ∀ w ∈ G.source e,
            Port.map deleteFresh.toFun (FocusErasure.contract
              (focussed G v term notOutput mode free) (.inr 0) rfl (split G v w)) = w := by
          intro w _
          rw [erase_contract, collapse_split]
        simpa only [List.map_id, Function.comp_def] using (List.map_congr_left (f := _) (g := id) point)
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))
  target := by
    rintro ⟨e, ne⟩
    cases e with
    | inl e =>
        change (((G.target e).map (host G)).map _).map _ = G.target e
        simp only [List.map_map]
        have point : ∀ w ∈ G.target e,
            Port.map deleteFresh.toFun (FocusErasure.contract
              (focussed G v term notOutput mode free) (.inr 0) rfl (host G w)) = w := by
          intro w _
          rw [erase_contract, collapse_host]
        simpa only [List.map_id, Function.comp_def] using (List.map_congr_left (f := _) (g := id) point)
    | inr i => exact False.elim (ne (congrArg Sum.inr (Fin.ext (by omega))))

/-- The target chosen by general erasure is the inserted fresh vertex. -/
theorem targetVertex_eq : (focussed G v term notOutput mode free).targetVertex = .inr 0 := by
  exact Port.internal.inj (focussed G v term notOutput mode free).targetVertex_spec.symm

/-- The choice-based underlying-graph operation also cancels insertion. -/
noncomputable def underlying_iso : Net.Iso (focussed G v term notOutput mode free).underlying G := by
  have eq : (focussed G v term notOutput mode free).underlying =
      erasedInsertion G v term notOutput mode free := by
    simp only [Focussed.underlying, targetVertex_eq]
  exact eq ▸ erase_iso G v term notOutput mode free


/-- The cancellation isomorphism also restores the distinguished joined vertex. -/
theorem underlying_position_exists :
    ∃ a : Net.Iso (focussed G v term notOutput mode free).underlying G,
      Port.map a.vertices.toFun
        (FocusErasure.position (focussed G v term notOutput mode free)
          (focussed G v term notOutput mode free).targetVertex
          (focussed G v term notOutput mode free).targetVertex_spec) = v := by
  have aux : ∀ t (ht : (focussed G v term notOutput mode free).target = Port.internal t),
      ∃ a : Net.Iso (FocusErasure.erase (focussed G v term notOutput mode free) t ht) G,
        Port.map a.vertices.toFun
          (FocusErasure.position (focussed G v term notOutput mode free) t ht) = v := by
    intro t ht
    have eq : t = .inr 0 := Port.internal.inj ht.symm
    subst t
    exact ⟨erase_iso G v term notOutput mode free, erase_position G v term notOutput mode free⟩
  exact aux _ _

end Hypernets.Linear.FocusInsertion
