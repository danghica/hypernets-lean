import Hypernets.Copying.ResourceGap

/-! The exact single weakening omitted by each injective atomic row embedding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Atomic
open Graph Opening

noncomputable def forestComplement (s : ShareSort) (d : Nat) {n m} (gap : ResourceGap n m) :
    Complement s (Distributor.atDepth s n 0 d) (Distributor.atDepth s m 0 d) where
  old := forestEmbedding s d gap.map gap.injective
  added := weakeningAt (Distributor.atDepth s m 0 d) ⟨gap.fresh,(0 : Fin 1)⟩ s ⟨gap.fresh.val,by simp⟩
    (by cases d <;> rfl) rfl rfl
  disjoint := by
    cases d <;> rintro ⟨i,e⟩ a eq
    all_goals exact gap.missing i (congrArg Sigma.fst eq)
  cover := by
    cases d <;> rintro ⟨i,e⟩
    all_goals
      rcases gap.cover i with ⟨a,eq⟩ | eq
      · subst i
        exact .inl ⟨⟨a,e⟩,rfl⟩
      · subst i
        have z : e = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst e
        exact .inr ⟨(0 : Fin 1),rfl⟩

theorem forestComplement_output (s : ShareSort) (d : Nat) {n m} (gap : ResourceGap n m) (i : Fin 1) :
    (forestComplement s d gap).added.ports (.output i) = .output ⟨gap.fresh.val,by simp⟩ :=
  by
  unfold forestComplement
  exact weakeningAt_output _ _ _ _ _ _ _ i

noncomputable def selectedRawComplement (s : ShareSort) (d : Nat) {n m} (gap : ResourceGap n m) (i : Fin n) :
    Complement s (SelectedResource.raw s d i) (SelectedResource.raw s d (gap.map i)) where
  old := SelectedResource.rawEmbedding s d gap.map gap.injective i
  added := weakeningAt _ (SelectedResource.edgeAt s d (gap.map i) (.inl gap.fresh)) s
    ⟨gap.fresh.val,by rw [SelectedResource.output_length]; exact gap.fresh.isLt⟩
    (SelectedResource.label_at s d (gap.map i) (.inl gap.fresh))
    (by rw [SelectedResource.source_eq]; rfl)
    (by rw [SelectedResource.target_eq]; simp only [SelectedResource.target,
          show gap.fresh ≠ gap.map i from Ne.symm (gap.missing i),↓reduceIte,List.map_singleton]; rfl)
  disjoint := by
    intro e a eq
    rw [weakeningAt_edge] at eq
    have h := congrArg (SelectedResource.edgeIndex s d (gap.map i)) eq
    change SelectedResource.edgeIndex s d (gap.map i)
      (SelectedResource.edgeAt s d (gap.map i) (Sum.map gap.map id (SelectedResource.edgeIndex s d i e))) = _ at h
    rw [SelectedResource.edgeIndex_at,SelectedResource.edgeIndex_at] at h
    cases old : SelectedResource.edgeIndex s d i e with
    | inl j => exact gap.missing j (Sum.inl.inj (old ▸ h))
    | inr u => simp only [old,Sum.map_inr,id_eq] at h; cases h
  cover e := by
    have eq := SelectedResource.edgeAt_index s d (gap.map i) e
    generalize tag : SelectedResource.edgeIndex s d (gap.map i) e = x at eq
    cases x with
    | inl j =>
      rcases gap.cover j with ⟨a,rfl⟩ | rfl
      · refine .inl ⟨SelectedResource.edgeAt s d i (.inl a),?_⟩
        change SelectedResource.edgeAt s d (gap.map i) (Sum.map gap.map id (SelectedResource.edgeIndex s d i _)) = _
        rw [SelectedResource.edgeIndex_at]
        exact eq
      · refine .inr ⟨by cases d <;> exact (0 : Fin 1),?_⟩
        rw [weakeningAt_edge]
        exact eq
    | inr u =>
      refine .inl ⟨SelectedResource.edgeAt s d i (.inr u),?_⟩
      change SelectedResource.edgeAt s d (gap.map i)
        (Sum.map gap.map (id : Unit → Unit) (SelectedResource.edgeIndex s d i (SelectedResource.edgeAt s d i (.inr u)))) = e
      rw [SelectedResource.edgeIndex_at]
      exact eq

noncomputable def selectedComplement (s : ShareSort) (d : Nat) {n m} (gap : ResourceGap n m) (i : Fin n) :
    Complement s (Translation.selectedResource d s i) (Translation.selectedResource d s (gap.map i)) :=
  (selectedRawComplement s d gap i).castInterfaces
    (SelectedResource.input_interface s i) (SelectedResource.output_interface s i)
    (SelectedResource.input_interface s (gap.map i)) (SelectedResource.output_interface s (gap.map i))

theorem selectedComplement_old (s : ShareSort) (d : Nat) {n m} (gap : ResourceGap n m) (i : Fin n) :
    (selectedComplement s d gap i).old = SelectedResource.embedding s d gap.map gap.injective i :=
  Complement.castInterfaces_old _ _ _ _ _

theorem selectedComplement_output (s : ShareSort) (d : Nat) {n m} (gap : ResourceGap n m) (i : Fin n) (j : Fin 1) :
    (selectedComplement s d gap i).added.ports (.output j) = .output ⟨gap.fresh.val,by simp⟩ :=
  by
  have out : (selectedRawComplement s d gap i).added.ports (.output j) =
      .output ⟨gap.fresh.val,by rw [SelectedResource.output_length]; exact gap.fresh.isLt⟩ := by
    unfold selectedRawComplement
    exact weakeningAt_output _ _ _ _ _ _ _ j
  exact (selectedRawComplement s d gap i).castInterfaces_added_output
    (SelectedResource.input_interface s i) (SelectedResource.output_interface s i)
    (SelectedResource.input_interface s (gap.map i)) (SelectedResource.output_interface s (gap.map i)) j _ out
end Hypernets.Copying.Weakening.Atomic
