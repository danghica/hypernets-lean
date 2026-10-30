import Hypernets.Copying.BoxPullContractionCopyReconstruction

/-! Exhaustive edge coverage of the actual BPullC correction. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

theorem normalization_copies_edge (e : (CopyRule.copies T H).Edge) :
    (rawNormalizationOccurrence T s H).edges (by cases d <;> exact ⟨false,⟨false,e⟩⟩) =
      (correctedCopies T s H).edges e := by cases d <;> rfl

theorem normalization_term_edge (i : Fin (variables s k 2)) (e : (CanonicalTree.atDepth .term 2 d).Edge) :
    (rawNormalizationOccurrence T s H).edges (by cases d <;> exact ⟨false,⟨true,⟨false,⟨i,e⟩⟩⟩⟩) =
      (termRow T s H i).edges e := by cases d <;> rfl

theorem normalization_atom_edge (i : Fin (atoms s h 2)) (e : (CanonicalTree.atDepth .atom 2 d).Edge) :
    (rawNormalizationOccurrence T s H).edges (by cases d <;> exact ⟨false,⟨true,⟨true,⟨i,e⟩⟩⟩⟩) =
      (atomRow T s H i).edges e := by cases d <;> rfl

theorem normalization_root_edge (e : (primitiveNet d (.contraction s)).Edge) :
    (rawNormalizationOccurrence T s H).edges (by cases d <;> exact ⟨true,e⟩) =
      (insertedContraction T s H).edges e := by cases d <;> rfl

/-- Original payload and residual-tree edges retain explicit preimages. -/
theorem copies_covered (e : (CopyRule.copies T H).Edge) :
    ∃ a, (rawNormalizationOccurrence T s H).edges a = (correctedCopies T s H).edges e :=
  ⟨_,normalization_copies_edge T s H e⟩

/-- Account for the two inserted canonical rows and their outside root. -/
theorem inserted_covered (e : (outside d s).Edge) :
    ∃ a, (rawNormalizationOccurrence T s H).edges a = (inserted T s H).edges e := by
  cases d
  all_goals
    obtain ⟨b,e⟩ := e
    cases b
    · obtain ⟨j,e⟩ := e
      cases s
      · let i : Fin (k+2) := ⟨k+j.val,by have := j.isLt; omega⟩
        refine ⟨_,(normalization_term_edge T .term H i e).trans ?_⟩
        have before : ¬ i.val < k := by dsimp [i]; omega
        simp only [termRow,dite_eq_right before]
        have eq : (⟨i.val-k,by dsimp [i]; have := j.isLt; omega⟩ : Fin 2) = j := Fin.ext (by simp [i])
        rw [eq]
        rfl
      · let i : Fin (2+h) := ⟨j.val,by have := j.isLt; omega⟩
        refine ⟨_,(normalization_atom_edge T .atom H i e).trans ?_⟩
        have selected : i.val < 2 := j.isLt
        simp only [atomRow,dite_eq_left selected]
        rfl
    · exact ⟨_,normalization_root_edge T s H e⟩

/-- Every retained old edge is either an original copy/tree edge or an
unselected distributor edge; the other five old edges were actually removed. -/
theorem raw_normalization_surjective : Function.Surjective (rawNormalizationOccurrence T s H).edges := by
  cases d
  all_goals
    intro edge
    cases edge with
    | inr edge => exact inserted_covered T s H edge
    | inl edge =>
      rcases edge with ⟨edge,notNone⟩
      cases edge with
      | none => exact False.elim (notNone rfl)
      | some edge =>
        rcases edge with ⟨old,kept⟩
        rcases old with ⟨part,old⟩
        cases part
        · rcases old with ⟨branch,old⟩
          cases branch
          · rcases old with ⟨payload,old⟩
            cases payload
            · exact copies_covered T s H ⟨false,old⟩
            · change Fin 1 at old
              have only : old = (0 : Fin 1) := Subsingleton.elim _ _
              subst old
              exact False.elim (kept ⟨false,⟨false,(0 : Fin 1)⟩⟩ rfl)
          · rcases old with ⟨component,old⟩
            cases component
            · exact copies_covered T s H ⟨true,⟨false,old⟩⟩
            · rcases old with ⟨payload,old⟩
              cases payload
              · exact copies_covered T s H ⟨true,⟨true,old⟩⟩
              · change Fin 1 at old
                have only : old = (0 : Fin 1) := Subsingleton.elim _ _
                subst old
                exact False.elim (kept ⟨false,⟨true,(0 : Fin 1)⟩⟩ rfl)
        · rcases old with ⟨sort,old⟩
          cases sort
          · rcases old with ⟨i,old⟩
            cases s
            · by_cases selected : i.val = k
              · have index : i = ⟨k,by change k < k+1; exact Nat.lt_succ_self k⟩ := Fin.ext selected
                subst i
                exact False.elim (kept ⟨true,old⟩ rfl)
              · let j : Fin (k+2) := ⟨i.val,by have := i.isLt; change i.val < k+1 at this; omega⟩
                refine ⟨_,(normalization_term_edge T .term H j old).trans ?_⟩
                have before : j.val < k := by dsimp [j]; have := i.isLt; change i.val < k+1 at this; omega
                simp only [termRow,dite_eq_left before]
                rfl
            · refine ⟨_,(normalization_term_edge T .atom H i old).trans ?_⟩
              rfl
          · rcases old with ⟨i,old⟩
            cases s
            · refine ⟨_,(normalization_atom_edge T .term H i old).trans ?_⟩
              rfl
            · by_cases selected : i.val = 0
              · have index : i = ⟨0,by change 0 < 1+h; exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_add_right 1 h)⟩ := Fin.ext selected
                subst i
                exact False.elim (kept ⟨true,old⟩ rfl)
              · let j : Fin (2+h) := ⟨i.val+1,by have := i.isLt; change i.val < 1+h at this; omega⟩
                refine ⟨_,(normalization_atom_edge T .atom H j old).trans ?_⟩
                have unselected : ¬ j.val < 2 := by dsimp [j]; omega
                simp only [atomRow,dite_eq_right unselected]
                have index : (⟨j.val-1,by dsimp [j]; have := i.isLt; change i.val < 1+h at this; omega⟩ : Fin (1+h)) = i :=
                  Fin.ext (by simp [j])
                simp only [index]
                rfl

private theorem occurrence_cast_surjective {r I O J K} {A B : Hypernet r I O} {C : Hypernet r J K}
    (eq : A = B) (f : Occurrence B C) (cover : Function.Surjective f.edges) :
    Function.Surjective ((congrArg (fun X => Occurrence X C) eq).mpr f).edges := by
  cases eq
  exact cover

/-- Every edge of the computed sharing correction occurs in the literal
outside-contraction reduct, with no omitted canonical weakening edges. -/
theorem normalization_surjective :
    Function.Surjective (normalizationOccurrence T s H).edges := by
  unfold normalizationOccurrence
  exact occurrence_cast_surjective (contract_eq s (CopyRule.after T H))
    (rawNormalizationOccurrence T s H) (raw_normalization_surjective T s H)

end Hypernets.Copying.BoxPullContraction.CopyRows
