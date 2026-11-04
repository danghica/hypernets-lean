import Hypernets.Copying.WeakeningBinaryRow

/-! Exhaustive whole-graph partition for binary weakening with independent
operands. Every retained or removed edge is identified explicitly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Pair
open Graph Opening BoxPullWeakening
variable {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

/-- The complete unused row shares no edge with either old operand or old row. -/
theorem row_old_disjoint : ∀ a b, (unusedRow G H s).edges a ≠ (old G H s).edges b := by
  cases d <;> cases s
  all_goals
    rintro ⟨a,e⟩ ⟨b,c⟩ eq
    cases a <;> cases b
    · rcases e with ⟨a,e⟩; rcases c with ⟨b,c⟩
      cases a <;> cases b <;> cases eq
    · rcases e with ⟨a,e⟩; cases a <;> cases eq
    · cases eq
    · rcases c with ⟨b,c⟩
      cases b
      all_goals first
        | cases eq
        | (rcases c with ⟨i,c⟩
           have middle := eq_of_heq (Sigma.mk.inj eq).2
           have inner := eq_of_heq (Sigma.mk.inj middle).2
           have resources := congrArg Sigma.fst inner
           have values := congrArg Fin.val resources
           have bound := i.isLt
           simp only [BoxPullWeakening.RetainedCopy.termResource] at values
           omega)

/-- No host edge is unaccounted for: the two new weakenings and their selected
canonical row form one part, and both old operands and all old rows the other. -/
theorem edge_cover (e : (core (extend G s) (extend H s)).Edge) :
    (∃ a, (unusedRow G H s).edges a = e) ∨ ∃ b, (old G H s).edges b = e := by
  cases d <;> cases s
  all_goals
    rcases e with ⟨a,e⟩
    cases a
    · rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨tag,e⟩
        cases tag
        · exact .inr ⟨⟨false,⟨false,e⟩⟩,rfl⟩
        · have zero : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
          subst e
          exact .inl ⟨⟨false,⟨false,(0 : Fin 1)⟩⟩,rfl⟩
      · rcases e with ⟨tag,e⟩
        cases tag
        · exact .inr ⟨⟨false,⟨true,e⟩⟩,rfl⟩
        · have zero : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
          subst e
          exact .inl ⟨⟨false,⟨true,(0 : Fin 1)⟩⟩,rfl⟩
    · rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨i,e⟩
        first
        | exact .inr ⟨⟨true,⟨false,⟨i,e⟩⟩⟩,rfl⟩
        | (by_cases last : i.val = k
           · have eq : i = ⟨k,by change k < k+1; omega⟩ := Fin.ext last
             refine .inl ⟨⟨true,e⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk false)
             exact congrArg (fun j : Fin (k+1) => (⟨j,e⟩ : Σ _ : Fin (k+1), Fin 3)) eq.symm
           · let j : Fin k := ⟨i.val,by have bound := i.isLt; change i.val < k+1 at bound; omega⟩
             have eq : i = BoxPullWeakening.RetainedCopy.termResource .term j := Fin.ext rfl
             refine .inr ⟨⟨true,⟨false,⟨j,e⟩⟩⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk false)
             exact congrArg (fun j : Fin (k+1) => (⟨j,e⟩ : Σ _ : Fin (k+1), Fin 3)) eq.symm)
      · rcases e with ⟨i,e⟩
        first
        | exact .inr ⟨⟨true,⟨true,⟨i,e⟩⟩⟩,rfl⟩
        | (by_cases zero : i.val = 0
           · have eq : i = ⟨0,by change 0 < h+1; omega⟩ := Fin.ext zero
             refine .inl ⟨⟨true,e⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk true)
             exact congrArg (fun j : Fin (h+1) => (⟨j,e⟩ : Σ _ : Fin (h+1), Fin 3)) eq.symm
           · let j : Fin h := ⟨i.val-1,by have bound := i.isLt; change i.val < h+1 at bound; omega⟩
             have eq : i = BoxPullWeakening.RetainedCopy.atomResource .atom j := Fin.ext (by change i.val = (i.val-1)+1; omega)
             refine .inr ⟨⟨true,⟨true,⟨j,e⟩⟩⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk true)
             exact congrArg (fun j : Fin (h+1) => (⟨j,e⟩ : Σ _ : Fin (h+1), Fin 3)) eq.symm)

/-- All geometric obligations of the general two-Idem reconstruction are
proved for the actual binary translation core, with unrelated operands. -/
noncomputable def partition : RowPartition.Partition s (core G H) (core (extend G s) (extend H s)) where
  row := unusedRow G H s
  old := old G H s
  disjoint := row_old_disjoint G H s
  cover := edge_cover G H s
  input := old_input G H s
  output := old_output G H s
  row_output := unusedRow_output G H s

/-- Pairing and the original distributor preserve recursive focus freedom. -/
theorem core_free (g : FocusFree G) (h : FocusFree H) : FocusFree (core G H) :=
  Serial.allLabels_net _ (by rintro ⟨b,e⟩; cases b; exact g e; exact h e)
    (Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _))

/-- Exact binary weakening: both independent added resources contract to one
outside weakening, with all original old-resource distributors retained. -/
noncomputable def normalize (g : FocusFree G) (h : FocusFree H) :
    Calculation (core (extend G s) (extend H s)) (extend (core G H) s) :=
  RowPartition.normalize (partition G H s) (core_free _ _
    ((extend_allLabels _ G s).mpr ⟨g,by intro mode eq; cases eq⟩)
    ((extend_allLabels _ H s).mpr ⟨h,by intro mode eq; cases eq⟩))

end Hypernets.Copying.Weakening.Pair
