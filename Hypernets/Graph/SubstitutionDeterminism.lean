import Hypernets.Graph.SubstitutionRefocusing

/-! Independence of the context decomposition used by substitution. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- On uniquely focussed graphs, recursive graph isomorphism preserves the focus. -/
def Focussed.deepIsoOfGraph {I O} {G H : Hypernet ops d I O} {f : Focussed G} {g : Focussed H}
    (a : Linear.DeepIso G H) : Focussed.DeepIso f g := by
  have eq : focusLabel ops d f.mode = primitiveLabel ops d (.focus f.mode) := by cases d <;> rfl
  have label := (labelEquiv_primitive (a.edge_label f.edge) (.focus f.mode) (f.label.trans eq)).trans eq.symm
  exact ⟨a,(g.mode_of_label label).symm,g.edge_of_label label⟩

namespace Substitution
/-- Relabel the unique selected variable as the resumed search focus. -/
noncomputable abbrev resumeVariable {I O} (G : Hypernet ops d I O) (v : G.Edge)
    (variableLabel : G.edgeLabel v = primitiveLabel ops d .variable) : Hypernet ops d I O := by
  classical
  exact G.relabelEdges (alphabet ops d).signature
    (fun e => if e = v then focusLabel ops d .search else G.edgeLabel e)
    (by intro e; by_cases eq : e = v
        · subst e; simp only [ite_true,variableLabel]; cases d <;> rfl
        · simp only [ite_false,eq])
    (by intro e; by_cases eq : e = v
        · subst e; simp only [ite_true,variableLabel]; cases d <;> rfl
        · simp only [ite_false,eq])

/-- Relabelling corresponding variables respects every recursive graph isomorphism. -/
noncomputable def resumeVariable_iso {I O} {G H : Hypernet ops d I O}
    (a : DeepIso G H) (v : G.Edge) (w : H.Edge)
    (vl : G.edgeLabel v = primitiveLabel ops d .variable)
    (wl : H.edgeLabel w = primitiveLabel ops d .variable) (same : a.edges.toFun v = w) :
    DeepIso (resumeVariable G v vl) (resumeVariable H w wl) where
  vertices := a.vertices
  edges := a.edges
  internal_label := a.internal_label
  source := a.source
  target := a.target
  edge_label := by
    classical
    intro e
    change LabelEquiv ops d (if e = v then focusLabel ops d .search else G.edgeLabel e)
      (if a.edges.toFun e = w then focusLabel ops d .search else H.edgeLabel (a.edges.toFun e))
    by_cases eq : e = v
    · subst e
      split
      · simpa [same] using labelEquiv_refl ops d (focusLabel ops d .search)
      · rename_i bad; exact False.elim (bad rfl)
    · have ne : a.edges.toFun e ≠ w := fun h => eq (a.edges.injective (h.trans same.symm))
      simp only [ite_false,eq,ne]
      exact a.edge_label e

/-- A substitution presentation names the same graph before removing the old
focus, and identifies the variable that becomes the new focus. -/
structure Presentation (s t : State ops d) where
  base : Hypernet ops d [.term] []
  free : FocusFree base
  closed : HoleFree base
  point : TypedPosition base
  mode : point.val.1 = .rewrite
  edge : base.Edge
  label : base.edgeLabel edge = primitiveLabel ops d .variable
  source : base.source edge = [point.val.2]
  left : Nonempty (Focussed.DeepIso (point.realize free closed).focussed s.focussed)
  right : Nonempty (DeepIso (resumeVariable base edge label) t.graph)

/-- Two decompositions of the same source choose the same variable after
transport along the underlying-graph isomorphism, hence have isomorphic reducts. -/
theorem Presentation.deterministic {s t u : State ops d}
    (a : Presentation s t) (b : Presentation s u) : Nonempty (Focussed.DeepIso t.focussed u.focussed) := by
  obtain ⟨left⟩ := a.left
  obtain ⟨right⟩ := b.left
  obtain ⟨iso,point⟩ := a.point.realization_coordinate_iso b.point a.free a.closed b.free b.closed (left.trans right.symm)
  have source : b.base.source (iso.edges.toFun a.edge) = [b.point.val.2] := by
    rw [← iso.source,a.source]
    exact congrArg List.singleton (congrArg (fun p => p.val.2) point)
  have edge : iso.edges.toFun a.edge = b.edge := b.base.source_unique
    (v := b.point.val.2) (by rw [source]; simp) (by rw [b.source]; simp)
  obtain ⟨leftResult⟩ := a.right
  obtain ⟨bu⟩ := b.right
  exact ⟨Focussed.deepIsoOfGraph (DeepIso.trans (DeepIso.symm leftResult)
    (DeepIso.trans (resumeVariable_iso iso a.edge b.edge a.label b.label edge) bu))⟩

/-- The relabelled variable-prefix graph is exactly the ordinary reduct,
including arbitrary equal-interface transport and all surrounding context edges. -/
noncomputable def resume_prefix_iso (C : Hypernet ops d [.term] []) (e : C.Edge)
    {O} (G : Hypernet ops d [.term] O)
    (hi : [.term] = (alphabet ops d).signature.input (C.edgeLabel e))
    (ho : O = (alphabet ops d).signature.output (C.edgeLabel e)) :
    Net.Iso (resumeVariable (C.plug e ((prefixVariable G).reboundary hi ho))
      (.inr (.inr 0)) rfl) (C.plug e ((after G).reboundary hi ho)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  source x := by
    change ((C.plug e ((prefixVariable G).reboundary hi ho)).source x).map (Port.map id) = _
    have mapId : Port.map (id : (C.Internal ⊕ (G.Internal ⊕ Fin 1)) → _) =
        (id : Port (C.Internal ⊕ (G.Internal ⊕ Fin 1)) 1 0 → _) := by
      funext v; cases v <;> rfl
    apply Eq.trans ((congrArg (fun f => List.map f _) mapId).trans (List.map_id _))
    cases x with
    | inl x => rfl
    | inr x => cases x with
      | inr j => rfl
      | inl x =>
          dsimp only [Net.plug,Net.Replacement.source,Net.Replacement.target,Net.reboundary,
            prefixVariable,after,FocusInsertion.insert,FocusInsertion.source,FocusInsertion.target,Bijection.refl,id]
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v with
          | internal v => rfl
          | output j => rfl
          | input j =>
              have eq : j = 0 := Fin.ext (by have h := j.isLt; change j.val < 1 at h; change j.val = 0; omega)
              subst j
              rfl
  target x := by
    change ((C.plug e ((prefixVariable G).reboundary hi ho)).target x).map (Port.map id) = _
    have mapId : Port.map (id : (C.Internal ⊕ (G.Internal ⊕ Fin 1)) → _) =
        (id : Port (C.Internal ⊕ (G.Internal ⊕ Fin 1)) 1 0 → _) := by
      funext v; cases v <;> rfl
    apply Eq.trans ((congrArg (fun f => List.map f _) mapId).trans (List.map_id _))
    cases x with
    | inl x => rfl
    | inr x => cases x with
      | inr j => rfl
      | inl x =>
          dsimp only [Net.plug,Net.Replacement.source,Net.Replacement.target,Net.reboundary,
            prefixVariable,after,FocusInsertion.insert,FocusInsertion.source,FocusInsertion.target,Bijection.refl,id]
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> rfl
  edge_label x := by
    dsimp only [resumeVariable,Net.relabelEdges,Bijection.refl]
    split
    · rename_i eq
      subst x
      rfl
    · rename_i ne
      cases x with
      | inl x => rfl
      | inr x => cases x with
        | inl x => rfl
        | inr j =>
            have eq : j = 0 := Fin.ext (by have bound := j.isLt; change j.val < 1 at bound; change j.val = 0; omega)
            exact False.elim (ne (congrArg (fun j => Sum.inr (Sum.inr j)) eq))

/-- Every concrete substitution supplies the canonical presentation used in the
uniqueness proof; this is derived from its witnesses rather than assumed. -/
theorem presentation {s t : State ops d} (step : State.Substitution s t) :
    Nonempty (Presentation s t) := by
  obtain ⟨C,e,⟨simple⟩,O,G,free,closed,hi,ho,⟨left⟩,⟨right⟩⟩ := step
  let H := (prefixVariable G).reboundary hi ho
  let i : Fin ((alphabet ops d).signature.input (C.edgeLabel e)).length := ⟨0,by simp [← hi]⟩
  have term : H.vertexLabel (.input i) = .term := by
    change ((alphabet ops d).signature.input (C.edgeLabel e))[i] = .term
    have helper : ∀ (I' : List Wire) (h : [.term] = I'), I'[0]'(by simp [← h]) = .term := by
      intro I' h; subst I'; rfl
    exact helper _ hi
  obtain ⟨fg,hg⟩ := StationaryPlug.filled_conditions C e H simple (variable_free G free)
    (holeFree_transport (variable_closed G closed) hi ho)
  let point : TypedPosition (C.plug e H) :=
    ⟨(.rewrite,Net.Replacement.insert C e H (.input i)),
      (Net.Replacement.insert_label C e H (.input i)).trans term⟩
  have l : Net.Iso (C.plug e (PlugFocusInsertion.fragment C e H i term .rewrite)) s.graph := by
    have eq := transport_insert (prefixVariable G) hi ho Focus.rewrite
    change (before G).reboundary hi ho = PlugFocusInsertion.fragment C e H i term .rewrite at eq
    rw [← eq]; exact left
  refine ⟨{
    base := C.plug e H, free := fg, closed := hg, point := point, mode := rfl,
    edge := .inr (.inr 0), label := rfl, source := ?_,
    left := ⟨Focussed.DeepIso.ofIso (Focussed.isoOfGraph ((PlugFocusInsertion.iso C e H i term .rewrite).symm.trans l))⟩,
    right := ⟨DeepIso.ofIso ((resume_prefix_iso C e G hi ho).trans right)⟩ }⟩
  rfl

end Substitution
namespace State
/-- Substitution is deterministic modulo recursive focus-preserving isomorphism,
even when the two steps use unrelated contexts and different fragment boundaries. -/
theorem substitution_deterministic {s t u : State ops d}
    (left : Substitution s t) (right : Substitution s u) :
    Nonempty (Focussed.DeepIso t.focussed u.focussed) := by
  obtain ⟨a⟩ := Linear.Substitution.presentation left
  obtain ⟨b⟩ := Linear.Substitution.presentation right
  exact a.deterministic b
end State
end Hypernets.Linear
