import Hypernets.Graph.PatternPlugging

/-! Incoming and outgoing subdivision agree at internal ports, up to names. -/
namespace Hypernets.Linear.FocusSubdivision
open Graph FocusInsertion
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (G : Hypernet ops d I O)

/-- Exchange the selected old internal vertex with the new focus vertex. -/
noncomputable def swap (v : G.Internal) : Bijection (G.Internal ⊕ Fin 1) (G.Internal ⊕ Fin 1) := by
  classical
  let f : G.Internal ⊕ Fin 1 → G.Internal ⊕ Fin 1 := fun x => match x with
    | .inl x => if x = v then .inr 0 else .inl x
    | .inr _ => .inl v
  have invol : ∀ x, f (f x) = x := by
    intro x
    cases x with
    | inl x => by_cases h : x = v <;> simp [f,h]
    | inr i => have h : i = 0 := Fin.ext (by omega); subst i; simp [f]
  exact ⟨f,f,invol,invol⟩

theorem swap_host (v : G.Internal) (w : G.Vertex) :
    Port.map (swap G v).toFun (host G w) = split G (.internal v) w := by
  classical
  cases w with
  | internal w => by_cases h : w = v <;> simp [swap,host,split,fresh,Port.map,h]
  | input i => simp [host,split,Port.map]
  | output i => simp [host,split,Port.map]

theorem swap_fresh (v : G.Internal) : Port.map (swap G v).toFun (fresh G) = host G (.internal v) := rfl

theorem swap_split (v : G.Internal) (w : G.Vertex) :
    Port.map (swap G v).toFun (split G (.internal v) w) = host G w := by
  rw [← swap_host]
  exact (Port.bijection (swap G v)).left_inv _

/-- Both orientations construct the same subdivided graph at an internal port. -/
noncomputable def iso (v : G.Internal) (term : G.internalLabel v = .term) (m : Focus) :
    Net.Iso (OutputFocusInsertion.insert G (.internal v) term (by intro h; cases h) m)
      (FocusInsertion.insert G (.internal v) term (by intro h; cases h) m) where
  vertices := swap G v
  edges := Bijection.refl _
  internal_label := by
    classical
    intro x
    cases x with
    | inl x => by_cases h : x = v <;> simp [swap,FocusInsertion.insert,OutputFocusInsertion.insert,internalLabel,h,term]
    | inr i => exact term
  edge_label := by intro e; cases e <;> rfl
  source := by
    intro e
    cases e with
    | inl e =>
        change ((G.source e).map (host G)).map _ = (G.source e).map (split G (.internal v))
        rw [List.map_map]
        exact List.map_congr_left (fun w _ => swap_host G v w)
    | inr i => exact congrArg List.singleton (swap_fresh G v)
  target := by
    intro e
    cases e with
    | inl e =>
        change ((G.target e).map (split G (.internal v))).map _ = (G.target e).map (host G)
        rw [List.map_map]
        exact List.map_congr_left (fun w _ => swap_split G v w)
    | inr i =>
        change [Port.map (swap G v).toFun (host G (.internal v))] = [fresh G]
        rw [swap_host]
        simp [split]

end Hypernets.Linear.FocusSubdivision
