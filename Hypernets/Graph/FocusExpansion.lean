import Hypernets.Graph.FocusContexts

/-! Extending a simultaneous filling across an inserted focus. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Linear.FocusExpansion
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}
    (C : Hypernet ops d [.term] [])
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (q : TypedPosition C)

noncomputable abbrev inserted := FocusInsertion.insert C q.val.2 q.property q.not_output q.val.1

/-- Keep the old fillings and retain the newly inserted focus as its corolla. -/
noncomputable abbrev family : (e : (inserted C q).Edge) → Hypernet ops d
    ((alphabet ops d).signature.input ((inserted C q).edgeLabel e))
    ((alphabet ops d).signature.output ((inserted C q).edgeLabel e))
  | .inl e => H e
  | .inr _ => Net.corolla (alphabet ops d).signature (focusLabel ops d q.val.1)

/-- Reassociate host vertices, filling vertices, and the fresh focus target. -/
noncomputable def vertices : Bijection ((inserted C q).expand (family C H q)).Internal
    ((C.expand H).Internal ⊕ Fin 1) where
  toFun
    | .inl (.inl v) => .inl (.inl v)
    | .inl (.inr i) => .inr i
    | .inr ⟨.inl e,v⟩ => .inl (.inr ⟨e,v⟩)
    | .inr ⟨.inr _,v⟩ => nomatch v
  invFun
    | .inl (.inl v) => .inl (.inl v)
    | .inl (.inr ⟨e,v⟩) => .inr ⟨.inl e,v⟩
    | .inr i => .inl (.inr i)
  left_inv := by
    rintro ((v | i) | ⟨e,v⟩)
    · rfl
    · rfl
    · cases e with
      | inl e => rfl
      | inr i => exact nomatch v
  right_inv := by rintro ((v | ⟨e,v⟩) | i) <;> rfl

/-- Old expansion edges are retained; the extra corolla contributes one focus. -/
noncomputable def edges : Bijection ((inserted C q).expand (family C H q)).Edge
    ((C.expand H).Edge ⊕ Fin 1) where
  toFun | ⟨.inl e,x⟩ => .inl ⟨e,x⟩ | ⟨.inr _,i⟩ => .inr i
  invFun | .inl ⟨e,x⟩ => ⟨.inl e,x⟩ | .inr i => ⟨.inr 0,i⟩
  left_inv := by
    rintro ⟨e,x⟩
    cases e with
    | inl e => rfl
    | inr i => have eq : i = 0 := Fin.ext (by omega); subst i; rfl
  right_inv := by rintro (⟨e,x⟩ | i) <;> rfl

/-- A retained host port has the same image under either order of construction. -/
theorem host (v : C.Vertex) :
    Port.map (vertices C H q).toFun
      (Net.Expansion.host (inserted C q) (family C H q) (FocusInsertion.host C v)) =
    FocusInsertion.host (C.expand H) (Net.Expansion.host C H v) := by cases v <;> rfl

/-- Splitting the chosen host port commutes with the reassociation. -/
theorem split (v : C.Vertex) :
    Port.map (vertices C H q).toFun
      (Net.Expansion.host (inserted C q) (family C H q) (FocusInsertion.split C q.val.2 v)) =
    FocusInsertion.split (C.expand H) (Net.Expansion.host C H q.val.2) (Net.Expansion.host C H v) := by
  classical
  by_cases eq : v = q.val.2
  · subst v; simp [FocusInsertion.split,Net.Expansion.host,FocusInsertion.fresh,Port.map,vertices]
  · have ne : Net.Expansion.host C H v ≠ Net.Expansion.host C H q.val.2 :=
      fun h => eq (Net.Expansion.host_injective C H h)
    simpa only [FocusInsertion.split,ite_eq_right eq,ite_eq_right ne] using host C H q v

/-- A filling source maps to the same split expanded port. -/
theorem source_port (e : C.Edge) (v : (H e).Vertex) (no : ¬ v.IsOutput) :
    Port.map (vertices C H q).toFun
      (Net.Expansion.insert (inserted C q) (family C H q) (.inl e) v) =
    FocusInsertion.split (C.expand H) (Net.Expansion.host C H q.val.2) (Net.Expansion.insert C H e v) := by
  classical
  cases v with
  | internal v =>
    have ne := (Net.Expansion.host_ne_internal C H q.val.2 e v).symm
    simp only [Net.Expansion.insert,FocusInsertion.split]
    rw [ite_eq_right ne]
    rfl
  | input i =>
    change Port.map (vertices C H q).toFun
      (Net.Expansion.host _ _ ((inserted C q).sourcePort (.inl e) i)) = _
    have eq : (inserted C q).sourcePort (.inl e) i = FocusInsertion.split C q.val.2 (C.sourcePort e i) := by
      simp only [Net.sourcePort,FocusInsertion.source,List.getElem_map]
    rw [eq]
    exact split C H q _
  | output i => exact False.elim (no trivial)

/-- A filling target maps to the retained expanded port. -/
theorem target_port (e : C.Edge) (v : (H e).Vertex) (no : ¬ v.IsInput) :
    Port.map (vertices C H q).toFun
      (Net.Expansion.insert (inserted C q) (family C H q) (.inl e) v) =
    FocusInsertion.host (C.expand H) (Net.Expansion.insert C H e v) := by
  cases v with
  | internal v => rfl
  | input i => exact False.elim (no trivial)
  | output i =>
    change Port.map (vertices C H q).toFun
      (Net.Expansion.host _ _ ((inserted C q).targetPort (.inl e) i)) = _
    have eq : (inserted C q).targetPort (.inl e) i = FocusInsertion.host C (C.targetPort e i) := by
      simp only [Net.targetPort,FocusInsertion.target,List.getElem_map]
    rw [eq]
    exact host C H q _

/-- Focus insertion commutes with arbitrary simultaneous filling. -/
noncomputable def iso : Net.Iso ((inserted C q).expand (family C H q))
    (FocusInsertion.insert (C.expand H) (q.expand H).val.2 (q.expand H).property
      (q.expand H).not_output q.val.1) where
  vertices := vertices C H q
  edges := edges C H q
  internal_label := by
    rintro ((v | i) | ⟨e,v⟩)
    · rfl
    · rfl
    · cases e with
      | inl e => rfl
      | inr i => exact nomatch v
  edge_label := by rintro ⟨e,x⟩; cases e <;> rfl
  source := by
    rintro ⟨e,x⟩
    cases e with
    | inl e =>
      change (((H e).source x).map _).map _ = (((H e).source x).map _).map _
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro v hv
      exact source_port C H q e v ((H e).source_not_output hv)
    | inr i =>
      have eq : i = 0 := Fin.ext (by omega); subst i
      have src : (Net.corolla (alphabet ops d).signature (focusLabel ops d q.val.1)).source x = [.input ⟨0,by cases d <;> exact Nat.zero_lt_succ 0⟩] := by
        cases d <;> rfl
      change (((family C H q (.inr 0)).source x).map _).map _ = [_]
      rw [src]
      simp only [List.map_cons,List.map_nil]
      apply congrArg (fun v => [v])
      change Port.map (vertices C H q).toFun
        (Net.Expansion.host (inserted C q) (family C H q) (FocusInsertion.host C q.val.2)) = _
      exact host C H q q.val.2
  target := by
    rintro ⟨e,x⟩
    cases e with
    | inl e =>
      change (((H e).target x).map _).map _ = (((H e).target x).map _).map _
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro v hv
      exact target_port C H q e v ((H e).target_not_input hv)
    | inr i =>
      have eq : i = 0 := Fin.ext (by omega); subst i
      have tgt : (Net.corolla (alphabet ops d).signature (focusLabel ops d q.val.1)).target x = [.output ⟨0,by cases d <;> exact Nat.zero_lt_succ 0⟩] := by
        cases d <;> rfl
      change (((family C H q (.inr 0)).target x).map _).map _ = [_]
      rw [tgt]
      rfl
end Hypernets.Linear.FocusExpansion
