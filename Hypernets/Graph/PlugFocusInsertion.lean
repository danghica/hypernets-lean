import Hypernets.Graph.HoleContextSearch

/-! Focus insertion at an input commutes with arbitrary shallow plugging. -/
namespace Hypernets.Linear.PlugFocusInsertion
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}

/-- Reassociate the retained, inserted, and fresh singleton carriers. -/
def reassoc (A B D : Type) : Bijection (A ⊕ (B ⊕ D)) ((A ⊕ B) ⊕ D) where
  toFun | .inl a => .inl (.inl a) | .inr (.inl b) => .inl (.inr b) | .inr (.inr c) => .inr c
  invFun | .inl (.inl a) => .inl a | .inl (.inr b) => .inr (.inl b) | .inr c => .inr (.inr c)
  left_inv x := by rcases x with a | (b | c) <;> rfl
  right_inv x := by rcases x with (a | b) | c <;> rfl

variable (C : Hypernet ops d I O) (e : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (i : Fin ((alphabet ops d).signature.input (C.edgeLabel e)).length)
    (term : H.vertexLabel (.input i) = .term) (m : Focus)

noncomputable abbrev fragment := FocusInsertion.insert H (.input i) term (by intro h; cases h) m
noncomputable abbrev whole := FocusInsertion.insert (C.plug e H)
  (Net.Replacement.insert C e H (.input i)) ((Net.Replacement.insert_label C e H (.input i)).trans term)
  (by simpa only [Net.Replacement.insert,Net.Replacement.host,Port.map_isOutput] using
    C.source_not_output (C.sourcePort_mem e i)) m

theorem host (v : C.Vertex) :
    Port.map (reassoc C.Internal H.Internal (Fin 1)).toFun
      (Net.Replacement.host C e (fragment C e H i term m) v) =
    FocusInsertion.host (C.plug e H) (Net.Replacement.host C e H v) := by cases v <;> rfl

theorem insert_host (v : H.Vertex) :
    Port.map (reassoc C.Internal H.Internal (Fin 1)).toFun
      (Net.Replacement.insert C e (fragment C e H i term m) (FocusInsertion.host H v)) =
    FocusInsertion.host (C.plug e H) (Net.Replacement.insert C e H v) := by
  cases v with
  | internal v => rfl
  | input j => exact host C e H i term m _
  | output j => exact host C e H i term m _

theorem insert_split (v : H.Vertex) (no : ¬ v.IsOutput) :
    Port.map (reassoc C.Internal H.Internal (Fin 1)).toFun
      (Net.Replacement.insert C e (fragment C e H i term m) (FocusInsertion.split H (.input i) v)) =
    FocusInsertion.split (C.plug e H) (Net.Replacement.insert C e H (.input i))
      (Net.Replacement.insert C e H v) := by
  classical
  by_cases eq : v = .input i
  · subst v
    simp [FocusInsertion.split,FocusInsertion.fresh,Net.Replacement.insert,Port.map,reassoc]
  · have ne : Net.Replacement.insert C e H v ≠ Net.Replacement.insert C e H (.input i) :=
      fun h => eq (Net.Replacement.insert_source_injective C e H no (by intro h; cases h) h)
    simp only [FocusInsertion.split,ite_eq_right eq,ite_eq_right ne]
    exact insert_host C e H i term m v

/-- Inserting at a replacement input and then plugging gives exactly insertion
at the corresponding whole-graph port, up to reassociation of fresh carriers. -/
noncomputable def iso : Net.Iso (C.plug e (fragment C e H i term m)) (whole C e H i term m) where
  vertices := reassoc _ _ _
  edges := reassoc _ _ _
  internal_label := by intro x; rcases x with a | (b | c) <;> rfl
  edge_label := by intro x; rcases x with a | (b | c) <;> rfl
  source := by
    intro x
    rcases x with x | (x | x)
    · change ((C.source x.val).map _).map _ = ((C.source x.val).map _).map _
      simp only [List.map_map]
      apply List.map_congr_left
      intro v hv
      have ne : Net.Replacement.host C e H v ≠ Net.Replacement.insert C e H (.input i) := by
        intro eq
        have same := Net.Replacement.host_injective C e H eq
        exact x.property (C.source_unique hv (same.symm ▸ C.sourcePort_mem e i))
      exact (host C e H i term m v).trans (by simp [FocusInsertion.split,ne])
    · change (((H.source x).map _).map _).map _ = ((H.source x).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v hv => insert_split C e H i term m v (H.source_not_output hv))
    · change [Port.map _ (Net.Replacement.insert C e (fragment C e H i term m)
        (FocusInsertion.host H (.input i)))] = [FocusInsertion.host (C.plug e H) (Net.Replacement.insert C e H (.input i))]
      exact congrArg List.singleton (insert_host C e H i term m (.input i))
  target := by
    intro x
    rcases x with x | (x | x)
    · change ((C.target x.val).map _).map _ = ((C.target x.val).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => host C e H i term m v)
    · change (((H.target x).map _).map _).map _ = ((H.target x).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => insert_host C e H i term m v)
    · rfl
end Hypernets.Linear.PlugFocusInsertion
