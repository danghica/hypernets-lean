import Hypernets.Graph.DeepSearchRenaming

/-! Focus insertion commutes with graph isomorphism, including its distinguished
edge and mode. -/
namespace Hypernets.Linear.FocusInsertion
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    {G H : Hypernet ops d I O} (a : DeepIso G H)

theorem deepRename_host (w : G.Vertex) :
    Port.map (a.vertices.sum (Bijection.refl (Fin 1))).toFun (host G w) =
      host H (Port.map a.vertices.toFun w) := by cases w <;> rfl

theorem deepRename_fresh :
    Port.map (a.vertices.sum (Bijection.refl (Fin 1))).toFun (fresh G) = fresh H := rfl

theorem deepRename_split (v w : G.Vertex) :
    Port.map (a.vertices.sum (Bijection.refl (Fin 1))).toFun (split G v w) =
      split H (Port.map a.vertices.toFun v) (Port.map a.vertices.toFun w) := by
  classical
  have eq : Port.map a.vertices.toFun w = Port.map a.vertices.toFun v ↔ w = v :=
    ⟨(Port.bijection a.vertices).injective, congrArg _⟩
  by_cases h : w = v
  · simp [split, h, deepRename_fresh]
  · simp [split, h, eq, deepRename_host]

/-- Extend both name bijections by fixing the newly inserted singleton names. -/
noncomputable def deepRename_iso (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) :
    DeepIso (insert G v term notOutput mode)
      (insert H (Port.map a.vertices.toFun v) ((deepIso_vertexLabel a v).trans term)
        (by simpa only [Port.map_isOutput] using notOutput) mode) where
  vertices := a.vertices.sum (Bijection.refl _)
  edges := a.edges.sum (Bijection.refl _)
  internal_label := by
    intro x
    cases x with
    | inl x => exact a.internal_label x
    | inr i => rfl
  edge_label := by
    intro e
    cases e with
    | inl e => exact a.edge_label e
    | inr i => exact labelEquiv_refl ops d _
  source := by
    intro e
    cases e with
    | inl e =>
        change ((G.source e).map (split G v)).map _ =
          (H.source (a.edges.toFun e)).map (split H (Port.map a.vertices.toFun v))
        rw [← a.source, List.map_map, List.map_map]
        apply List.map_congr_left
        intro w _
        exact deepRename_split a v w
    | inr i =>
        change [Port.map _ (host G v)] = [host H (Port.map a.vertices.toFun v)]
        rw [deepRename_host]
  target := by
    intro e
    cases e with
    | inl e =>
        change ((G.target e).map (host G)).map _ = (H.target (a.edges.toFun e)).map (host H)
        rw [← a.target, List.map_map, List.map_map]
        apply List.map_congr_left
        intro w _
        exact deepRename_host a w
    | inr i => rfl

/-- The extended isomorphism preserves the actual inserted focus. -/
noncomputable def deepRename_focussed (v : G.Vertex) (term : G.vertexLabel v = .term)
    (notOutput : ¬ v.IsOutput) (mode : Focus) (freeG : FocusFree G) (freeH : FocusFree H) :
    Focussed.DeepIso (focussed G v term notOutput mode freeG)
      (focussed H (Port.map a.vertices.toFun v) ((deepIso_vertexLabel a v).trans term)
        (by simpa only [Port.map_isOutput] using notOutput) mode freeH) where
  graph := deepRename_iso a v term notOutput mode
  mode := rfl
  focus := rfl

end Hypernets.Linear.FocusInsertion

namespace Hypernets.Linear.TypedPosition
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {G H : Hypernet ops d [.term] []}

/-- Realization is compatible with renaming its underlying typed coordinate. -/
noncomputable def realize_deepRename (a : DeepIso G H) (p : TypedPosition G)
    (fg : FocusFree G) (hg : HoleFree G) (fh : FocusFree H) (hh : HoleFree H) :
    Focussed.DeepIso (p.realize fg hg).focussed ((p.deepRename a).realize fh hh).focussed :=
  FocusInsertion.deepRename_focussed a p.val.2 p.property p.not_output p.val.1 fg fh

end Hypernets.Linear.TypedPosition
