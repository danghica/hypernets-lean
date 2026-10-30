import Hypernets.Copying.BoxPullContractionRetainedCopy
import Hypernets.Copying.BoxPullContractionCutLinks

/-! Reconstruct each original resource distributor after the literal
four-input interchange, using the inserted rows only at the two selected ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph Opening
variable {d n k h : Nat} (T : ContractionTree .term (n+1)) (s : ShareSort)
  (H : Hypernet d [.term] (environmentInterface (variables s k 2) (atoms s h 2)))

/-- Original term row in the actual reduct before the interchange. -/
def originalTermRow (i : Fin (variables s k 1)) :
    Occurrence (CanonicalTree.atDepth .term 2 d) (CopyRule.after T (merged s H)) :=
  (BoxPullWeakening.CopyRow.termOccurrence d (variables s k 1) (atoms s h 1) i).comp
    (Occurrence.serialRight _ _)

def originalAtomRow (i : Fin (atoms s h 1)) :
    Occurrence (CanonicalTree.atDepth .atom 2 d) (CopyRule.after T (merged s H)) :=
  (BoxPullWeakening.CopyRow.atomOccurrence d (variables s k 1) (atoms s h 1) i).comp
    (Occurrence.serialRight _ _)

theorem originalTermRow_disjoint (i : Fin (variables s k 1)) (unselected : s = .term → i.val ≠ k) :
    ∀ a b, (insideOccurrence T s H).edges a ≠ (originalTermRow T s H i).edges b := by
  cases d <;> cases s
  all_goals
    rintro ⟨a,e⟩ b eq
    cases a
    · rcases e with ⟨c,e⟩; cases c <;> cases eq
    · first
      | (cases eq <;> exact unselected rfl rfl)
      | (have p := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2)
         exact unselected rfl (congrArg Fin.val p).symm)
  all_goals exact unselected rfl rfl

theorem originalAtomRow_disjoint (i : Fin (atoms s h 1)) (unselected : s = .atom → i.val ≠ 0) :
    ∀ a b, (insideOccurrence T s H).edges a ≠ (originalAtomRow T s H i).edges b := by
  cases d <;> cases s
  all_goals
    rintro ⟨a,e⟩ b eq
    cases a
    · rcases e with ⟨c,e⟩; cases c <;> cases eq
    · first
      | (cases eq <;> exact unselected rfl rfl)
      | (have p := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2)
         exact unselected rfl (congrArg Fin.val p).symm)
  all_goals exact unselected rfl rfl

noncomputable def retainedTermRow (i : Fin (variables s k 1)) (unselected : s = .term → i.val ≠ k) :
    Occurrence (CanonicalTree.atDepth .term 2 d) (corrected T s H) :=
  (insideOccurrence T s H).acrossCut (originalTermRow T s H i)
    (originalTermRow_disjoint T s H i unselected) (outside d s)

noncomputable def retainedAtomRow (i : Fin (atoms s h 1)) (unselected : s = .atom → i.val ≠ 0) :
    Occurrence (CanonicalTree.atDepth .atom 2 d) (corrected T s H) :=
  (insideOccurrence T s H).acrossCut (originalAtomRow T s H i)
    (originalAtomRow_disjoint T s H i unselected) (outside d s)

/-- One of the two canonical rows in the literal seven-edge replacement. -/
noncomputable def insertedRow (j : Fin 2) : Occurrence (CanonicalTree.atDepth s 2 d) (corrected T s H) :=
  ((BoxPullWeakening.CopyRow.forestOccurrence s 2 2 d j).comp
    (BoxPullWeakening.RetainedCopy.serialLeftOccurrence _ _)).comp (inserted T s H)

/-- The two selected resource rows have their original copy-major order. -/
theorem insertedRow_input (j : Fin 2) (b : Bool) :
    (insertedRow T s H j).ports (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) =
    (inserted T s H).ports (.input ⟨(if b then 2 else 0)+j.val,by cases b <;> simp <;> have := j.isLt <;> omega⟩) := by
  change (inserted T s H).ports (BoundarySerial.leftInsert _ _
    ((BoxPullWeakening.CopyRow.forestOccurrence s 2 2 d j).ports _)) = _
  apply congrArg (inserted T s H).ports
  change BoundarySerial.leftInsert _ _ (.input _) = _
  rw [Combined.left_input]
  apply congrArg Port.input
  apply Fin.ext
  cases b <;> simp [Distributor.boundary,Distributor.inputIndex,FinGrid.index,Nat.add_comm]

/-- The replaced rows reattach to the exact original selected copy outputs. -/
theorem corrected_selected_link (j : Fin 2) (b : Bool) :
    (correctedCopies T s H).ports
      (.output (CopyRule.copyOutput (variables s k 2) (atoms s h 2) b (resource s j))) =
    (insertedRow T s H j).ports (.input ⟨if b then 1 else 0,by cases b <;> simp⟩) := by
  rw [insertedRow_input]
  exact (insideOccurrence T s H).acrossCut_replacement_input (outside d s)
    (originalCopies T s H) (originalCopies_disjoint T s H) _ _ (inside_input_link T s H b j)

/-- Term resources use the inserted rows only in the two selected positions. -/
noncomputable def termRow (i : Fin (variables s k 2)) :
    Occurrence (CanonicalTree.atDepth .term 2 d) (corrected T s H) := by
  cases s
  · by_cases before : i.val < k
    · exact retainedTermRow T .term H ⟨i.val,by change i.val < k+1; omega⟩ (by intro _; dsimp; omega)
    · exact insertedRow T .term H ⟨i.val-k,by have := i.isLt; change i.val < k+2 at this; omega⟩
  · exact retainedTermRow T .atom H i (by intro eq; cases eq)

/-- Atom resources use the first two inserted rows precisely in the atom case. -/
noncomputable def atomRow (i : Fin (atoms s h 2)) :
    Occurrence (CanonicalTree.atDepth .atom 2 d) (corrected T s H) := by
  cases s
  · exact retainedAtomRow T .term H i (by intro eq; cases eq)
  · by_cases selected : i.val < 2
    · exact insertedRow T .atom H ⟨i.val,selected⟩
    · exact retainedAtomRow T .atom H ⟨i.val-1,by have := i.isLt; change i.val < 2+h at this; change i.val-1 < 1+h; omega⟩
        (by intro _; dsimp; omega)

end Hypernets.Copying.BoxPullContraction.CopyRows
