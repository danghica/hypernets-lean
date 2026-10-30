import Hypernets.Copying.BoxPullContractionForestPorts

/-! The reconstructed canonical rows are disjoint and assemble into the
complete original ordered environment distributor. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

theorem retainedTermRow_index {i j : Fin (variables s k 1)} {hi hj} {e c}
    (eq : (retainedTermRow T s H i hi).edges e = (retainedTermRow T s H j hj).edges c) : i = j := by
  cases d
  all_goals
    have base := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val (Sum.inl.inj eq)))
    exact congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj base).2)).2)

theorem retainedAtomRow_index {i j : Fin (atoms s h 1)} {hi hj} {e c}
    (eq : (retainedAtomRow T s H i hi).edges e = (retainedAtomRow T s H j hj).edges c) : i = j := by
  cases d
  all_goals
    have base := congrArg Subtype.val (Option.some.inj (congrArg Subtype.val (Sum.inl.inj eq)))
    exact congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj base).2)).2)

theorem insertedRow_index {i j : Fin 2} {e c}
    (eq : (insertedRow T s H i).edges e = (insertedRow T s H j).edges c) : i = j := by
  cases d
  all_goals exact congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2)

theorem termRows_disjoint : ∀ i j, i ≠ j → ∀ e c,
    (termRow T s H i).edges e ≠ (termRow T s H j).edges c := by
  cases s
  · intro i j ne e c eq
    by_cases bi : i.val < k <;> by_cases bj : j.val < k
    · simp only [termRow,dite_eq_left bi,dite_eq_left bj] at eq
      have same := congrArg Fin.val (retainedTermRow_index T .term H eq)
      exact ne (Fin.ext same)
    · simp only [termRow,dite_eq_left bi,dite_eq_right bj] at eq
      cases d <;> cases eq
    · simp only [termRow,dite_eq_right bi,dite_eq_left bj] at eq
      cases d <;> cases eq
    · simp only [termRow,dite_eq_right bi,dite_eq_right bj] at eq
      have same := congrArg Fin.val (insertedRow_index T .term H eq)
      apply ne
      apply Fin.ext
      change i.val-k = j.val-k at same
      omega
  · intro i j ne e c eq
    simp only [termRow] at eq
    exact ne (retainedTermRow_index T .atom H eq)

theorem atomRows_disjoint : ∀ i j, i ≠ j → ∀ e c,
    (atomRow T s H i).edges e ≠ (atomRow T s H j).edges c := by
  cases s
  · intro i j ne e c eq
    simp only [atomRow] at eq
    exact ne (retainedAtomRow_index T .term H eq)
  · intro i j ne e c eq
    by_cases bi : i.val < 2 <;> by_cases bj : j.val < 2
    · simp only [atomRow,dite_eq_left bi,dite_eq_left bj] at eq
      have same := congrArg Fin.val (insertedRow_index T .atom H eq)
      exact ne (Fin.ext same)
    · simp only [atomRow,dite_eq_left bi,dite_eq_right bj] at eq
      cases d <;> cases eq
    · simp only [atomRow,dite_eq_right bi,dite_eq_left bj] at eq
      cases d <;> cases eq
    · simp only [atomRow,dite_eq_right bi,dite_eq_right bj] at eq
      have same := congrArg Fin.val (retainedAtomRow_index T .atom H eq)
      apply ne
      apply Fin.ext
      change i.val-1 = j.val-1 at same
      omega

theorem term_atom_disjoint (i : Fin (variables s k 2)) (j : Fin (atoms s h 2))
    (e : (CanonicalTree.atDepth .term 2 d).Edge) (c : (CanonicalTree.atDepth .atom 2 d).Edge) :
    (termRow T s H i).edges e ≠ (atomRow T s H j).edges c := by
  intro eq
  cases s
  · by_cases before : i.val < k
    · simp only [termRow,dite_eq_left before,atomRow] at eq
      cases d <;> cases eq
    · simp only [termRow,dite_eq_right before,atomRow] at eq
      cases d <;> cases eq
  · by_cases selected : j.val < 2
    · simp only [termRow,atomRow,dite_eq_left selected] at eq
      cases d <;> cases eq
    · simp only [termRow,atomRow,dite_eq_right selected] at eq
      cases d <;> cases eq

noncomputable def termForest : Occurrence (Distributor.atDepth .term (variables s k 2) 2 d) (corrected T s H) :=
  (Occurrence.ofIso (BoxPullWeakening.RetainedCopy.forestIso d (variables s k 2) 2 .term)).comp
    (Occurrence.ParallelJoin.occurrence (fun _ : Fin (variables s k 2) => CanonicalTree.atDepth .term 2 d)
      (Distributor.boundary .term (variables s k 2) 2) (Enumeration.fin _)
      (termRow T s H) (termRows_disjoint T s H))

noncomputable def atomForest : Occurrence (Distributor.atDepth .atom (atoms s h 2) 2 d) (corrected T s H) :=
  (Occurrence.ofIso (BoxPullWeakening.RetainedCopy.forestIso d (atoms s h 2) 2 .atom)).comp
    (Occurrence.ParallelJoin.occurrence (fun _ : Fin (atoms s h 2) => CanonicalTree.atDepth .atom 2 d)
      (Distributor.boundary .atom (atoms s h 2) 2) (Enumeration.fin _)
      (atomRow T s H) (atomRows_disjoint T s H))

noncomputable def forests (b : Bool) :
    Occurrence (Net.Tensor.family (Distributor.atDepth .term (variables s k 2) 2 d)
      (Distributor.atDepth .atom (atoms s h 2) 2 d) b) (corrected T s H) :=
  match b with | false => termForest T s H | true => atomForest T s H

theorem forests_disjoint : ∀ a b, a ≠ b → ∀ e c,
    (forests T s H a).edges e ≠ (forests T s H b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · rcases e with ⟨i,e⟩; rcases c with ⟨j,c⟩
    exact term_atom_disjoint T s H i j e c eq
  · rcases e with ⟨i,e⟩; rcases c with ⟨j,c⟩
    exact term_atom_disjoint T s H j i c e eq.symm
  · exact ne rfl

/-- The full original resource forest is reconstructed, including every
canonical weakening and all unselected term and atom resources. -/
noncomputable def distributor :
    Occurrence (Translation.environmentDistributor d (variables s k 2) (atoms s h 2) 2) (corrected T s H) :=
  Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (Distributor.atDepth .term (variables s k 2) 2 d)
      (Distributor.atDepth .atom (atoms s h 2) 2 d))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (forests T s H) (forests_disjoint T s H)

end Hypernets.Copying.BoxPullContraction.CopyRows
