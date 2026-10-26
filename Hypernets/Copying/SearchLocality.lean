import Hypernets.Copying.SearchPadding

/-! Intrinsic search survives shallow context filling on both sides of the boundary. -/
namespace Hypernets.Copying.Search
open Graph

/-- The head of a context search interaction cannot be its hole. -/
theorem search_ne_hole {d I O} {G : Hypernet d I O} {e hole : G.Edge} {p : Primitive}
    (label : G.edgeLabel e = primitiveLabel d p) (h : Hole)
    (holeLabel : G.edgeLabel hole = primitiveLabel d (.hole h))
    {v : G.Vertex} {t} (result : enter p v (G.target e) = some t) : e ≠ hole := by
  intro eq
  subst hole
  have same := primitiveLabel_injective d (label.symm.trans holeLabel)
  subst p
  simp [enter] at result

/-- Search already present in the host persists when an unrelated hole is filled.
No injectivity of the context's attachment map is assumed. -/
theorem plug_host {d I O} {G : Hypernet d I O} {s t : Position G} (step : Step G s t)
    (hole : G.Edge) (h : Hole) (hl : G.edgeLabel hole = primitiveLabel d (.hole h))
    (H : Hypernet d ((alphabet d).signature.input (G.edgeLabel hole))
      ((alphabet d).signature.output (G.edgeLabel hole))) :
    Step (G.plug hole H) (s.1,Net.Replacement.host G hole H s.2)
      (t.1,Net.Replacement.host G hole H t.2) := by
  cases step with
  | search e p v t label src result =>
    have ne := search_ne_hole label h hl result
    apply Step.search (G := G.plug hole H) (.inl ⟨e,ne⟩) p _ _ label
    · exact List.mem_map_of_mem src
    · change enter p _ ((G.target e).map _) = _
      rw [enter_map,result]; rfl
  | backtrack e o root v i t label src bound arg result =>
    have ne : e ≠ hole := by
      intro eq
      have bad := primitiveLabel_injective d (label.symm.trans ((congrArg G.edgeLabel eq).trans hl))
      cases bad
    apply Step.backtrack (G := G.plug hole H) (.inl ⟨e,ne⟩) o (Net.Replacement.host G hole H root) _ i _ label
    · change (G.source e).map _ = _; rw [src]; rfl
    · exact bound
    · change ((G.target e).map _)[i]? = _; rw [List.getElem?_map,arg]; rfl
    · change resume o _ ((G.target e).map _) i = _; rw [resume_map,result]; rfl

/-- An interaction inside the inserted graph persists with its exact argument number. -/
theorem plug_insert {d I O} (G : Hypernet d I O) (hole : G.Edge)
    (H : Hypernet d ((alphabet d).signature.input (G.edgeLabel hole))
      ((alphabet d).signature.output (G.edgeLabel hole)))
    {s t : Position H} (step : Step H s t) :
    Step (G.plug hole H) (s.1,Net.Replacement.insert G hole H s.2)
      (t.1,Net.Replacement.insert G hole H t.2) := by
  cases step with
  | search e p v t label src result =>
    apply Step.search (G := G.plug hole H) (.inr e) p _ _ label
    · exact List.mem_map_of_mem src
    · change enter p _ ((H.target e).map _) = _; rw [enter_map,result]; rfl
  | backtrack e o root v i t label src bound arg result =>
    apply Step.backtrack (G := G.plug hole H) (.inr e) o (Net.Replacement.insert G hole H root) _ i _ label
    · change (H.source e).map _ = _; rw [src]; rfl
    · exact bound
    · change ((H.target e).map _)[i]? = _; rw [List.getElem?_map,arg]; rfl
    · change resume o _ ((H.target e).map _) i = _; rw [resume_map,result]; rfl

/-- Host search runs retain their exact length under context filling. -/
theorem plug_host_trace {d I O} {G : Hypernet d I O} {s t : Position G} {n}
    (run : Trace (Step G) s t n) (hole : G.Edge) (h : Hole)
    (hl : G.edgeLabel hole = primitiveLabel d (.hole h))
    (H : Hypernet d ((alphabet d).signature.input (G.edgeLabel hole))
      ((alphabet d).signature.output (G.edgeLabel hole))) :
    Trace (Step (G.plug hole H)) (s.1,Net.Replacement.host G hole H s.2)
      (t.1,Net.Replacement.host G hole H t.2) n :=
  run.map (fun x => (x.1,Net.Replacement.host G hole H x.2)) (fun step => plug_host step hole h hl H)

theorem plug_insert_trace {d I O} (G : Hypernet d I O) (hole : G.Edge)
    (H : Hypernet d ((alphabet d).signature.input (G.edgeLabel hole))
      ((alphabet d).signature.output (G.edgeLabel hole))) {s t : Position H} {n}
    (run : Trace (Step H) s t n) :
    Trace (Step (G.plug hole H)) (s.1,Net.Replacement.insert G hole H s.2)
      (t.1,Net.Replacement.insert G hole H t.2) n :=
  run.map (fun x => (x.1,Net.Replacement.insert G hole H x.2)) (fun step => plug_insert G hole H step)
end Hypernets.Copying.Search
