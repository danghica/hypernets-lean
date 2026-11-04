import Hypernets.Copying.ParametricityBareApply
import Hypernets.Copying.ParametricityLargeOpening
import Hypernets.Copying.RetainedBetaEnabled

/-! A large parametricity body exposes its callback argument as a term
output. The whole callback graph remains unevaluated and outside the family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareCall
open Graph Opening Combined
variable {d n : Nat} {hasPrivate : Bool}
    (F : Hypernet d (List.replicate (n+1) .term) [])
    (A : Hypernet d [.term] (LargeSplice.freeInterface hasPrivate))
    (B : Hypernet d [.term] [.term])
    (f : Occurrence A F) (attached : f.ports (.input 0) = .input ⟨0,by simp⟩)

def after := Serial.net (BareApplyFirst.net F) B
noncomputable def firstBlock : Occurrence (BareApplyFirst.net F) (after F B) :=
  BoxPullWeakening.ReverseComponents.serialLeft _ _
noncomputable def callback : Occurrence B (after F B) :=
  BoxPullWeakening.ReverseComponents.serialRight _ _
noncomputable def head : Occurrence (primitiveNet d (.operation .app)) (after F B) :=
  (BareApplyFirst.head F).comp (firstBlock F B)
noncomputable def selected : Occurrence A (after F B) :=
  (f.comp (BareApplyFirst.family F)).comp (firstBlock F B)

include attached in
theorem function_link : (head F B).ports (.output (0 : Fin 2)) =
    (selected F A B f).ports (.input 0) := by
  change (firstBlock F B).ports ((BareApplyFirst.head F).ports (.output (0 : Fin 2))) =
    (firstBlock F B).ports ((BareApplyFirst.family F).ports (f.ports (.input 0)))
  rw [attached,BareApplyFirst.head_function]

theorem argument_link : (head F B).ports (.output (1 : Fin 2)) =
    (callback F B).ports (.input 0) := by
  change (firstBlock F B).ports ((BareApplyFirst.head F).ports (.output (1 : Fin 2))) = _
  rw [BareApplyFirst.head_argument]
  exact BoxPullWeakening.ReverseComponents.serial_boundary _ _ _

theorem selected_callback_disjoint : ∀ e a, (selected F A B f).edges e ≠ (callback F B).edges a := by
  cases d <;> intro e a eq <;> cases eq

noncomputable def arguments : Occurrence (Net.Tensor.net A B) (after F B) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (selected F A B f) (callback F B)
    (selected_callback_disjoint F A B f)

include attached in
theorem argument_ports : ∀ i, (head F B).ports (.output i) =
    (arguments F A B f).ports (.input i) := by
  intro i
  change Fin 2 at i
  have choices : i=(0 : Fin 2) ∨ i=1 := by
    by_cases zero : i.val=0
    · exact .inl (Fin.ext zero)
    · exact .inr (Fin.ext (by have:=i.isLt;omega))
  rcases choices with rfl | rfl
  · exact (function_link F A B f attached).trans
      (Occurrence.tensorJoin_left (selected F A B f) (callback F B)
        (selected_callback_disjoint F A B f) (.input (0 : Fin 1))).symm
  · exact (argument_link F B).trans
      (Occurrence.tensorJoin_right (selected F A B f) (callback F B)
        (selected_callback_disjoint F A B f) (.input (0 : Fin 1))).symm

theorem head_arguments_disjoint : ∀ e a, (head F B).edges e ≠ (arguments F A B f).edges a := by
  cases d
  all_goals rintro e ⟨side,a⟩ eq; cases side <;> cases eq

/-- The entire original inner app, smaller lambda and callback occur with
their complete original bodies and ordered resource attachments. -/
noncomputable def rawOccurrence : Occurrence (LargeSplice.raw A B) (after F B) :=
  Occurrence.SerialJoin.occurrence (head F B) (arguments F A B f)
    (argument_ports F A B f attached) (head_arguments_disjoint F A B f)

noncomputable def bodyOccurrence : Occurrence (LargeSplice.body A B) (after F B) := by
  cases hasPrivate
  · exact rawOccurrence F A B f attached
  · exact (Occurrence.ofBoundaryIso (InterfacePermutation.iso (LargeSplice.raw A B) boundFirst).symm).comp
      (rawOccurrence F A B f attached)

theorem raw_input : (rawOccurrence F A B f attached).ports (.input 0) = .input ⟨0,by simp⟩ := by
  rw [rawOccurrence,Occurrence.SerialJoin.occurrence_input]
  cases d
  all_goals
    change BoundarySerial.leftInsert (BareApplyFirst.net F) B (.input ⟨0,by simp⟩) = _
    exact left_input _ _ _

theorem body_input : (bodyOccurrence F A B f attached).ports (.input 0) = .input ⟨0,by simp⟩ := by
  cases hasPrivate <;> exact raw_input F A B f attached

/-- The bound callback variable is the unchanged exposed term output,
including on the left where the original body output order is swapped. -/
theorem body_argument : (bodyOccurrence F A B f attached).ports (.output 0) = .output 0 := by
  cases hasPrivate
  all_goals
    change (rawOccurrence F A B f attached).ports (.output _) = _
    rw [rawOccurrence,Occurrence.SerialJoin.occurrence_output]
    change (arguments F A B f).ports
      ((BoxPullWeakening.ReverseComponents.tensorRight A B).ports (.output 0)) = _
    rw [arguments,Occurrence.tensorJoin_right]
    exact Application.right_serial_output _ _ _

end Hypernets.Copying.Parametricity.BareCall
