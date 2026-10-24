import Hypernets.Graph.OutputFocusInsertion
import Hypernets.Graph.LocalRewiring

/-! Factoring focus subdivisions through one-edge interaction fragments. -/
namespace Hypernets.Linear.PatternPlugging
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (C : Hypernet ops d I O) (e : C.Edge)

abbrev corolla := Net.corolla (alphabet ops d).signature (C.edgeLabel e)

/-- Remove the empty internal carrier of the operation corolla. -/
def vertices : Bijection (C.Internal ⊕ (Empty ⊕ Fin 1)) (C.Internal ⊕ Fin 1) where
  toFun | .inl x => .inl x | .inr (.inl x) => nomatch x | .inr (.inr x) => .inr x
  invFun | .inl x => .inl x | .inr x => .inr (.inr x)
  left_inv x := by rcases x with x | (x | x); rfl; exact nomatch x; rfl
  right_inv x := by cases x <;> rfl

/-- Retain the host edge names and restore the selected edge from its corolla. -/
noncomputable def edges : Bijection ({x : C.Edge // x ≠ e} ⊕ (Fin 1 ⊕ Fin 1)) (C.Edge ⊕ Fin 1) := by
  classical
  exact {
    toFun := fun x => match x with | .inl x => .inl x.val | .inr (.inl _) => .inl e | .inr (.inr x) => .inr x
    invFun := fun x => match x with
      | .inl x => if h : x = e then .inr (.inl 0) else .inl ⟨x,h⟩
      | .inr x => .inr (.inr x)
    left_inv := by
      intro x
      rcases x with x | (i | i)
      · simp [x.property]
      · have h : i = 0 := Fin.ext (by omega); subst i; simp
      · rfl
    right_inv := by intro x; cases x with
      | inl x => by_cases h : x = e <;> simp [h]
      | inr x => rfl }

section Input
variable (i : Fin ((alphabet ops d).signature.input (C.edgeLabel e)).length)
    (term : ((alphabet ops d).signature.input (C.edgeLabel e))[i] = .term) (m : Focus)

/-- The finite input-focused interaction fragment has precisely two edges. -/
noncomputable abbrev inputPattern :=
  FocusInsertion.insert (corolla C e) (.input i) term (by intro h; cases h) m

/-- The same subdivision performed directly in the host graph. -/
noncomputable abbrev inputWhole := FocusInsertion.insert C (C.sourcePort e i)
  ((C.sourcePort_label e i).trans term) (C.source_not_output (C.sourcePort_mem e i)) m

theorem input_host (v : C.Vertex) :
    Port.map (vertices C).toFun (Net.Replacement.host C e (inputPattern C e i term m) v) =
      FocusInsertion.host C v := by cases v <;> rfl

theorem input_insert_host (v : (corolla C e).Vertex) :
    Port.map (vertices C).toFun
      (Net.Replacement.insert C e (inputPattern C e i term m) (FocusInsertion.host (corolla C e) v)) =
      FocusInsertion.host C (match v with
        | .internal x => nomatch x | .input j => C.sourcePort e j | .output j => C.targetPort e j) := by
  cases v with
  | internal x => exact nomatch x
  | input j => exact input_host C e i term m _
  | output j => exact input_host C e i term m _

theorem input_insert_split (j : Fin ((alphabet ops d).signature.input (C.edgeLabel e)).length) :
    Port.map (vertices C).toFun
      (Net.Replacement.insert C e (inputPattern C e i term m)
        (FocusInsertion.split (corolla C e) (.input i) (.input j))) =
      FocusInsertion.split C (C.sourcePort e i) (C.sourcePort e j) := by
  classical
  by_cases h : j = i
  · subst j; simp [FocusInsertion.split,FocusInsertion.fresh,Net.Replacement.insert,Port.map,vertices]
  · have ne : C.sourcePort e j ≠ C.sourcePort e i := fun eq => h (C.sourcePort_injective e eq)
    simp only [FocusInsertion.split,Port.input.injEq,ite_eq_right h,ite_eq_right ne]
    exact input_insert_host C e i term m (.input j)

/-- Plugging the two-edge input fragment is exactly host focus subdivision. -/
noncomputable def input_iso : Net.Iso (C.plug e (inputPattern C e i term m)) (inputWhole C e i term m) where
  vertices := vertices C
  edges := edges C e
  internal_label := by intro x; rcases x with x | (x | x); rfl; exact nomatch x; rfl
  edge_label := by intro x; rcases x with x | (x | x) <;> rfl
  source := by
    intro x
    rcases x with x | (x | x)
    · change ((C.source x.val).map _).map _ = (C.source x.val).map _
      rw [List.map_map]
      apply List.map_congr_left
      intro v hv
      have ne : v ≠ C.sourcePort e i := by
        intro eq
        exact x.property (C.source_unique hv (eq ▸ C.sourcePort_mem e i))
      exact (input_host C e i term m v).trans (by simp [FocusInsertion.split,ne])
    · change ((((List.finRange _).map Port.input).map _).map _).map _ = (C.source e).map _
      rw [← Net.PlugUnit.sourcePort_list C e]
      simp only [List.map_map]
      exact List.map_congr_left (fun j _ => input_insert_split C e i term m j)
    · change [Port.map _ (Net.Replacement.insert C e (inputPattern C e i term m)
        (FocusInsertion.host (corolla C e) (.input i)))] = [FocusInsertion.host C (C.sourcePort e i)]
      exact congrArg List.singleton (input_insert_host C e i term m (.input i))
  target := by
    intro x
    rcases x with x | (x | x)
    · change ((C.target x.val).map _).map _ = (C.target x.val).map _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => input_host C e i term m v)
    · change ((((List.finRange _).map Port.output).map _).map _).map _ = (C.target e).map _
      rw [← Net.PlugUnit.targetPort_list C e]
      simp only [List.map_map]
      exact List.map_congr_left (fun j _ => input_insert_host C e i term m (.output j))
    · rfl

end Input

section Output
variable (i : Fin ((alphabet ops d).signature.output (C.edgeLabel e)).length)
    (term : ((alphabet ops d).signature.output (C.edgeLabel e))[i] = .term) (m : Focus)

/-- The finite output-focused interaction fragment has precisely two edges. -/
noncomputable abbrev outputPattern :=
  OutputFocusInsertion.insert (corolla C e) (.output i) term (by intro h; cases h) m

/-- The same subdivision performed directly in the host graph. -/
noncomputable abbrev outputWhole := OutputFocusInsertion.insert C (C.targetPort e i)
  ((C.targetPort_label e i).trans term) (C.target_not_input (C.targetPort_mem e i)) m

theorem output_host (v : C.Vertex) :
    Port.map (vertices C).toFun (Net.Replacement.host C e (outputPattern C e i term m) v) =
      FocusInsertion.host C v := by cases v <;> rfl

theorem output_insert_host (v : (corolla C e).Vertex) :
    Port.map (vertices C).toFun
      (Net.Replacement.insert C e (outputPattern C e i term m) (FocusInsertion.host (corolla C e) v)) =
      FocusInsertion.host C (match v with
        | .internal x => nomatch x | .output j => C.targetPort e j | .input j => C.sourcePort e j) := by
  cases v with
  | internal x => exact nomatch x
  | output j => exact output_host C e i term m _
  | input j => exact output_host C e i term m _

theorem output_insert_split (j : Fin ((alphabet ops d).signature.output (C.edgeLabel e)).length) :
    Port.map (vertices C).toFun
      (Net.Replacement.insert C e (outputPattern C e i term m)
        (FocusInsertion.split (corolla C e) (.output i) (.output j))) =
      FocusInsertion.split C (C.targetPort e i) (C.targetPort e j) := by
  classical
  by_cases h : j = i
  · subst j; simp [FocusInsertion.split,FocusInsertion.fresh,Net.Replacement.insert,Port.map,vertices]
  · have ne : C.targetPort e j ≠ C.targetPort e i := fun eq => h (C.targetPort_injective e eq)
    simp only [FocusInsertion.split,Port.output.injEq,ite_eq_right h,ite_eq_right ne]
    exact output_insert_host C e i term m (.output j)

/-- Plugging the two-edge output fragment is exactly host focus subdivision. -/
noncomputable def output_iso : Net.Iso (C.plug e (outputPattern C e i term m)) (outputWhole C e i term m) where
  vertices := vertices C
  edges := edges C e
  internal_label := by intro x; rcases x with x | (x | x); rfl; exact nomatch x; rfl
  edge_label := by intro x; rcases x with x | (x | x) <;> rfl
  target := by
    intro x
    rcases x with x | (x | x)
    · change ((C.target x.val).map _).map _ = (C.target x.val).map _
      rw [List.map_map]
      apply List.map_congr_left
      intro v hv
      have ne : v ≠ C.targetPort e i := by
        intro eq
        exact x.property (C.target_unique hv (eq ▸ C.targetPort_mem e i))
      exact (output_host C e i term m v).trans (by simp [FocusInsertion.split,ne])
    · change ((((List.finRange _).map Port.output).map _).map _).map _ = (C.target e).map _
      rw [← Net.PlugUnit.targetPort_list C e]
      simp only [List.map_map]
      exact List.map_congr_left (fun j _ => output_insert_split C e i term m j)
    · change [Port.map _ (Net.Replacement.insert C e (outputPattern C e i term m)
        (FocusInsertion.host (corolla C e) (.output i)))] = [FocusInsertion.host C (C.targetPort e i)]
      exact congrArg List.singleton (output_insert_host C e i term m (.output i))
  source := by
    intro x
    rcases x with x | (x | x)
    · change ((C.source x.val).map _).map _ = (C.source x.val).map _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => output_host C e i term m v)
    · change ((((List.finRange _).map Port.input).map _).map _).map _ = (C.source e).map _
      rw [← Net.PlugUnit.sourcePort_list C e]
      simp only [List.map_map]
      exact List.map_congr_left (fun j _ => output_insert_host C e i term m (.input j))
    · rfl

end Output

end Hypernets.Linear.PatternPlugging
