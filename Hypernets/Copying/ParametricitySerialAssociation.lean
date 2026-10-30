import Hypernets.Copying.OccurrenceCoverIso
import Hypernets.Copying.BoxPullWeakeningReverseLambda

/-! Serial reassociation preserves every ordered boundary and recursive edge
label. This is a graph isomorphism, not an observational equation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Serial.Association
open Graph Opening BoxPullWeakening
variable {d I J K O} (A : Hypernet d I J) (B : Hypernet d J K) (C : Hypernet d K O)

noncomputable def first := ReverseComponents.serialLeft A (Serial.net B C)
noncomputable def second := (ReverseComponents.serialLeft B C).comp (ReverseComponents.serialRight A (Serial.net B C))
noncomputable def third := (ReverseComponents.serialRight B C).comp (ReverseComponents.serialRight A (Serial.net B C))

theorem first_boundary (i : Fin J.length) :
    (first A B C).ports (.output i) = (second A B C).ports (.input i) := by
  change (ReverseComponents.serialLeft A (Serial.net B C)).ports (.output i) =
    (ReverseComponents.serialRight A (Serial.net B C)).ports (BoundarySerial.leftInsert B C (.input i))
  rw [Combined.left_input]
  exact ReverseComponents.serial_boundary _ _ i

theorem first_disjoint : ∀ e f, (first A B C).edges e ≠ (second A B C).edges f := by
  cases d <;> intro e f eq <;> cases congrArg Sigma.fst eq

noncomputable def pairOccurrence := Occurrence.SerialJoin.occurrence
  (first A B C) (second A B C) (first_boundary A B C) (first_disjoint A B C)

theorem second_boundary (i : Fin K.length) :
    (pairOccurrence A B C).ports (.output i) = (third A B C).ports (.input i) := by
  unfold pairOccurrence
  rw [Occurrence.SerialJoin.occurrence_output]
  exact congrArg (ReverseComponents.serialRight A (Serial.net B C)).ports
    (ReverseComponents.serial_boundary B C i)

theorem second_disjoint : ∀ e f, (pairOccurrence A B C).edges e ≠ (third A B C).edges f := by
  cases d <;> rintro ⟨b,e⟩ f eq <;> cases b
  all_goals solve
    | cases congrArg Sigma.fst eq
    | cases congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)

noncomputable def occurrence : Occurrence (Serial.net (Serial.net A B) C) (Serial.net A (Serial.net B C)) :=
  Occurrence.SerialJoin.occurrence (pairOccurrence A B C) (third A B C)
    (second_boundary A B C) (second_disjoint A B C)

theorem input (i : Fin I.length) : (occurrence A B C).ports (.input i) = .input i := by
  unfold occurrence pairOccurrence
  rw [Occurrence.SerialJoin.occurrence_input,Occurrence.SerialJoin.occurrence_input]
  exact Combined.left_input _ _ i

theorem output (i : Fin O.length) : (occurrence A B C).ports (.output i) = .output i := by
  unfold occurrence
  rw [Occurrence.SerialJoin.occurrence_output]
  change BoundarySerial.rightInsert _ _ (BoundarySerial.rightInsert _ _ (.output i)) = _
  rw [Application.right_serial_output,Application.right_serial_output]

theorem cover (e : (Serial.net A (Serial.net B C)).Edge) : ∃ a, (occurrence A B C).edges a = e := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | exact ⟨⟨false,⟨false,e⟩⟩,rfl⟩
    | (rcases e with ⟨b,e⟩; cases b
       · exact ⟨⟨false,⟨true,e⟩⟩,rfl⟩
       · exact ⟨⟨true,e⟩,rfl⟩)

noncomputable def iso : DeepIso (Serial.net (Serial.net A B) C) (Serial.net A (Serial.net B C)) :=
  (occurrence A B C).iso_of_edge_surjective (input A B C) (output A B C) (cover A B C)

end Hypernets.Copying.Serial.Association
