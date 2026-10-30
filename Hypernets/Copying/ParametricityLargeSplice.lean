import Hypernets.Copying.ParametricityPadding
import Hypernets.Copying.BoundaryOccurrence
import Hypernets.Copying.BoxPullWeakeningReverseBeta
import Hypernets.Copying.OccurrenceCoverIso

/-! The large parametricity beta reduct retains its inner lambda and the
entire unevaluated callback. The bound callback output is connected to V. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeSplice
open Graph Opening

def freeInterface (hasPrivate : Bool) : List Wire := if hasPrivate then [.term] else []
variable {d : Nat} {hasPrivate : Bool} {O : List Wire}
    (A : Hypernet d [.term] (freeInterface hasPrivate))
    (B : Hypernet d [.term] [.term]) (V : Hypernet d [.term] O)

def raw : Hypernet d [.term] (freeInterface hasPrivate ++ [.term]) :=
  Serial.net (primitiveNet d (.operation .app)) (Net.Tensor.net A B)

/-- The actual Figure20 left output swap selects f, while the right family
already has f as its sole output. No callback transition takes place here. -/
def body : Hypernet d [.term] (.term :: freeInterface hasPrivate) := by
  cases hasPrivate
  · exact raw A B
  · exact InterfacePermutation.net (raw A B) boundFirst

def source : Hypernet d [.term] (freeInterface hasPrivate ++ O) := Application.splice (body A B) V
def target : Hypernet d [.term] (freeInterface hasPrivate ++ O) :=
  Serial.net (primitiveNet d (.operation .app)) (Net.Tensor.net A (Serial.net B V))

noncomputable def rawOccurrence : Occurrence (raw A B) (body A B) := by
  cases hasPrivate
  · exact Occurrence.ofIso (DeepIso.refl _)
  · exact Occurrence.ofBoundaryIso (InterfacePermutation.iso (raw A B) boundFirst)

noncomputable def bodyOccurrence : Occurrence (body A B) (source A B V) := by
  cases d <;> exact Occurrence.expand (Application.splicePattern _ _ _)
    (Application.spliceFilling (body A B) V) false
noncomputable def argument : Occurrence V (source A B V) := by
  cases d <;> exact Occurrence.expand (Application.splicePattern _ _ _)
    (Application.spliceFilling (body A B) V) true
noncomputable def rawInSource := (rawOccurrence A B).comp (bodyOccurrence A B V)
noncomputable def head :=
  (BoxPullWeakening.ReverseComponents.serialLeft (primitiveNet d (.operation .app)) (Net.Tensor.net A B)).comp
    (rawInSource A B V)
noncomputable def arguments :=
  (BoxPullWeakening.ReverseComponents.serialRight (primitiveNet d (.operation .app)) (Net.Tensor.net A B)).comp
    (rawInSource A B V)
noncomputable def first := (BoxPullWeakening.ReverseComponents.tensorLeft A B).comp (arguments A B V)
noncomputable def callback := (BoxPullWeakening.ReverseComponents.tensorRight A B).comp (arguments A B V)

theorem callback_link : (callback A B V).ports (.output (0 : Fin 1)) =
    (argument A B V).ports (.input (0 : Fin 1)) := by
  cases hasPrivate <;> cases d <;> rfl

theorem callback_disjoint : ∀ e x, (callback A B V).edges e ≠ (argument A B V).edges x := by
  cases hasPrivate <;> cases d <;> intro e x eq <;> cases eq

noncomputable def appliedCallback : Occurrence (Serial.net B V) (source A B V) :=
  Occurrence.SerialJoin.occurrence (callback A B V) (argument A B V)
    (fun i => by change Fin 1 at i; have zero : i = (0 : Fin 1) := Subsingleton.elim _ _; subst i; exact callback_link A B V)
    (callback_disjoint A B V)

theorem first_disjoint : ∀ e x, (first A B V).edges e ≠ (appliedCallback A B V).edges x := by
  cases hasPrivate <;> cases d
  all_goals rintro e ⟨side,x⟩ eq
  all_goals cases side <;> cases eq

noncomputable def paired := BoxPullWeakening.ReverseComponents.tensorJoin
  (first A B V) (appliedCallback A B V) (first_disjoint A B V)

theorem head_link : ∀ i, (head A B V).ports (.output i) = (paired A B V).ports (.input i) := by
  intro i
  change Fin 2 at i
  have range : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
    by_cases zero : i.val = 0
    · exact .inl (Fin.ext zero)
    · exact .inr (Fin.ext (by have := i.isLt; omega))
  rcases range with rfl | rfl
  all_goals cases hasPrivate <;> cases d <;> rfl

theorem head_disjoint : ∀ e x, (head A B V).edges e ≠ (paired A B V).edges x := by
  cases hasPrivate <;> cases d
  all_goals
    rintro e ⟨side,x⟩ eq
    cases side
    · cases eq
    · rcases x with ⟨part,x⟩
      cases part <;> cases eq

noncomputable def occurrence : Occurrence (target A B V) (source A B V) :=
  Occurrence.SerialJoin.occurrence (head A B V) (paired A B V) (head_link A B V) (head_disjoint A B V)
theorem first_output (i : Fin (freeInterface hasPrivate).length) :
    (first A B V).ports (.output i) = .output ⟨i.val,by simp; have := i.isLt; omega⟩ := by
  cases hasPrivate
  · exact Fin.elim0 i
  · change Fin 1 at i
    have zero : i = 0 := Subsingleton.elim _ _
    subst i
    cases d <;> rfl

theorem argument_output (i : Fin O.length) :
    (argument A B V).ports (.output i) = Application.valuePort (freeInterface hasPrivate) O i := by
  cases d
  all_goals
    change Application.SpliceBoundary.rawArgumentInsert (body A B) V (.output i) = _
    rw [Application.SpliceBoundary.argument_insert]
    rfl

theorem paired_left_output (i : Fin (freeInterface hasPrivate).length) :
    (paired A B V).ports (.output (Net.Tensor.join (freeInterface hasPrivate) O ⟨false,i⟩)) =
      (first A B V).ports (.output i) := by
  change (paired A B V).ports (Net.Parallel.embed
    (Net.Tensor.family A (Serial.net B V)) (Net.Tensor.boundary _ _ _ _) false (.output i)) = _
  unfold paired BoxPullWeakening.ReverseComponents.tensorJoin
  apply Occurrence.ParallelJoin.occurrence_embed

theorem paired_right_output (i : Fin O.length) :
    (paired A B V).ports (.output (Net.Tensor.join (freeInterface hasPrivate) O ⟨true,i⟩)) =
      (argument A B V).ports (.output i) := by
  have eq : (paired A B V).ports (.output (Net.Tensor.join (freeInterface hasPrivate) O ⟨true,i⟩)) =
      (appliedCallback A B V).ports (.output i) := by
    change (paired A B V).ports (Net.Parallel.embed
      (Net.Tensor.family A (Serial.net B V)) (Net.Tensor.boundary _ _ _ _) true (.output i)) = _
    unfold paired BoxPullWeakening.ReverseComponents.tensorJoin
    apply Occurrence.ParallelJoin.occurrence_embed
  rw [eq,appliedCallback,Occurrence.SerialJoin.occurrence_output]

theorem cover : Function.Surjective (occurrence A B V).edges := by
  cases hasPrivate <;> cases d
  all_goals
    rintro ⟨part,e⟩
    cases part
    · rcases e with ⟨part,e⟩
      cases part
      · exact ⟨⟨false,e⟩,rfl⟩
      · rcases e with ⟨part,e⟩
        cases part
        · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
        · exact ⟨⟨true,⟨true,⟨false,e⟩⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,⟨true,e⟩⟩⟩,rfl⟩

theorem input (i : Fin [Wire.term].length) :
    (occurrence A B V).ports (.input i) = .input i := by
  change Fin 1 at i
  have zero : i = 0 := Subsingleton.elim _ _
  subst i
  cases hasPrivate <;> cases d <;> rfl

theorem output (i : Fin (freeInterface hasPrivate ++ O).length) :
    (occurrence A B V).ports (.output i) = .output i := by
  rw [occurrence,Occurrence.SerialJoin.occurrence_output]
  by_cases before : i.val < (freeInterface hasPrivate).length
  · let j : Fin (freeInterface hasPrivate).length := ⟨i.val,before⟩
    have index : i = Net.Tensor.join (freeInterface hasPrivate) O ⟨false,j⟩ := Fin.ext rfl
    rw [index,paired_left_output,first_output]
    rfl
  · let j : Fin O.length := ⟨i.val-(freeInterface hasPrivate).length,by have := i.isLt; simp at this; omega⟩
    have index : i = Net.Tensor.join (freeInterface hasPrivate) O ⟨true,j⟩ :=
      Fin.ext (by dsimp [j,Net.Tensor.join]; omega)
    rw [index,paired_right_output,argument_output]
    rfl

/-- The entire beta splice factors as the original inner lambda applied to
an unchanged callback graph connected to V. The callback need not terminate. -/
noncomputable def iso : DeepIso (target A B V) (source A B V) :=
  (occurrence A B V).iso_of_edge_surjective (input A B V) (output A B V) (cover A B V)

end Hypernets.Copying.Parametricity.LargeSplice
