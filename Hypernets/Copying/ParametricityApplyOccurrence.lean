import Hypernets.Copying.ParametricityApplyFirst
import Hypernets.Copying.OccurrenceTensorBoundary

/-! A selected member of a complete family gives an actual complete
application occurrence; all remaining family members and private wires stay
in its constructed complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ApplyFirst
open Graph Opening
variable {d n J O} {A : Hypernet d [.term] J}
    {G : Hypernet d (List.replicate (n+1) .term) []}
    (V : Hypernet d [.term] O) (f : Occurrence A G)
    (attached : f.ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩)

noncomputable def selected : Occurrence A (net G V) := f.comp (family G V)

theorem selected_argument_disjoint : ∀ e a, (selected V f).edges e ≠ (argument G V).edges a := by
  cases d <;> intro e a eq <;> cases eq

noncomputable def binaryArguments : Occurrence (Net.Tensor.net A V) (net G V) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (selected V f) (argument G V) (selected_argument_disjoint V f)

include attached in
theorem binary_link : ∀ i, (head G V).ports (.output i) = (binaryArguments V f).ports (.input i) := by
  intro i
  change Fin 2 at i
  have cases : i=(0 : Fin 2) ∨ i=1 := by
    by_cases z : i.val=0
    · exact .inl (Fin.ext z)
    · exact .inr (Fin.ext (by have := i.isLt; omega))
  rcases cases with rfl | rfl
  · have eq := Occurrence.tensorJoin_left (selected V f) (argument G V) (selected_argument_disjoint V f) (.input (0 : Fin 1))
    change (binaryArguments V f).ports (.input (0 : Fin 2)) = (family G V).ports (f.ports (.input (0 : Fin 1))) at eq
    rw [eq,attached]
    exact head_function G V
  · have eq := Occurrence.tensorJoin_right (selected V f) (argument G V) (selected_argument_disjoint V f) (.input (0 : Fin 1))
    change (binaryArguments V f).ports (.input (1 : Fin 2)) = (argument G V).ports (.input (0 : Fin 1)) at eq
    rw [eq]
    exact head_argument G V

theorem head_binary_disjoint : ∀ e a, (head G V).edges e ≠ (binaryArguments V f).edges a := by
  cases d
  all_goals rintro e ⟨part,a⟩ eq; cases part <;> cases eq

/-- The unchanged original app, selected family member and arbitrary argument
form a complete ordered local source, with no boundary or freshness premise. -/
noncomputable def binaryOccurrence : Occurrence
    (Serial.net (primitiveNet d (.operation .app)) (Net.Tensor.net A V)) (net G V) :=
  Occurrence.SerialJoin.occurrence (head G V) (binaryArguments V f) (binary_link V f attached) (head_binary_disjoint V f)

theorem binary_input : (binaryOccurrence V f attached).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  rw [binaryOccurrence,Occurrence.SerialJoin.occurrence_input]
  exact head_input G V

end Hypernets.Copying.Parametricity.ApplyFirst
