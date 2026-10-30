import Hypernets.Copying.OccurrenceBoundaryTarget
import Hypernets.Copying.ParametricityTailPrecompose
import Hypernets.Copying.OccurrenceTensorBoundary
import Hypernets.Copying.OccurrenceCoverIso

/-! After the private read returns its numeral, the remaining family attaches
only to the weakened original tree and cell. The numeral is a genuinely
separate component, not an observational simplification. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.TailPrecompose.TensorResult
open Graph Opening
variable {d n O} (P : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (A : Hypernet d [.term] []) (R : Hypernet d (List.replicate n .term) O)

def selected : Hypernet d (List.replicate (n+1) .term) O :=
  (Net.Tensor.net A R).reboundary (by simp [List.replicate_succ]) rfl

def source := net P (selected A R)
def target : Hypernet d (List.replicate (n+1) .term) O :=
  (Net.Tensor.net A (Serial.net P R)).reboundary (by simp [List.replicate_succ]) rfl

noncomputable def familyOccurrence : Occurrence P (source P A R) := leftOccurrence P (selected A R)
noncomputable def activeOccurrence : Occurrence A (source P A R) :=
  ((BoxPullWeakening.ReverseComponents.tensorLeft A R).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp (rightOccurrence P (selected A R))
noncomputable def remainderOccurrence : Occurrence R (source P A R) :=
  ((BoxPullWeakening.ReverseComponents.tensorRight A R).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp (rightOccurrence P (selected A R))

theorem link (i : Fin (List.replicate n Wire.term).length) :
    (familyOccurrence P A R).ports (.output i) = (remainderOccurrence P A R).ports (.input i) := by
  cases d
  all_goals
    change leftInsert P (selected A R) (.output i) =
      rightInsert P (selected A R) (.input ⟨1+i.val,by simp; have := i.isLt; simp only [List.length_replicate] at this; omega⟩)
    have idx : (⟨1+i.val,by simp; have := i.isLt; simp only [List.length_replicate] at this; omega⟩ : Fin (List.replicate (n+1) Wire.term).length) =
        ⟨i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := Fin.ext (Nat.add_comm _ _)
    rw [idx]
    exact (right_succ P (selected A R) ⟨i.val,by simpa using i.isLt⟩).symm

theorem family_remainder_disjoint : ∀ e a,
    (familyOccurrence P A R).edges e ≠ (remainderOccurrence P A R).edges a := by
  cases d <;> intro e a eq <;> cases eq

noncomputable def continuation : Occurrence (Serial.net P R) (source P A R) :=
  Occurrence.SerialJoin.occurrence (familyOccurrence P A R) (remainderOccurrence P A R)
    (link P A R) (family_remainder_disjoint P A R)

theorem active_disjoint : ∀ e a,
    (activeOccurrence P A R).edges e ≠ (continuation P A R).edges a := by
  cases d
  all_goals
    rintro e ⟨part,a⟩ eq
    cases part <;> cases eq

noncomputable def occurrence : Occurrence (target P A R) (source P A R) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (activeOccurrence P A R)
    (continuation P A R) (active_disjoint P A R)).reboundarySource _ _

theorem active_input : (activeOccurrence P A R).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  cases d <;> exact right_zero P (selected A R)

theorem continuation_input (i : Fin (List.replicate n Wire.term).length) :
    (continuation P A R).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  rw [continuation,Occurrence.SerialJoin.occurrence_input]
  cases d <;> exact left_input P (selected A R) i

theorem remainder_output (i : Fin O.length) :
    (remainderOccurrence P A R).ports (.output i) = .output i := by
  cases d
  all_goals
    change rightInsert P (selected A R) (.output ⟨0+i.val,by omega⟩) = _
    have idx : (⟨0+i.val,by omega⟩ : Fin O.length) = i := Fin.ext (Nat.zero_add _)
    rw [idx,right_output]

theorem input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (occurrence P A R).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    change (BoxPullWeakening.ReverseComponents.tensorJoin (activeOccurrence P A R) (continuation P A R) (active_disjoint P A R)).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft A (Serial.net P R)).ports (.input (0 : Fin 1))) = _
    rw [Occurrence.tensorJoin_left]
    exact active_input P A R
  · let j : Fin (List.replicate n Wire.term).length := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at *; omega⟩
    have eq : (BoxPullWeakening.ReverseComponents.tensorRight A (Serial.net P R)).ports (.input j) =
        .input (⟨i.val,by have h:=i.isLt; simp only [List.length_replicate,List.length_append,List.length_cons,List.length_nil] at *; omega⟩ : Fin ([Wire.term]++List.replicate n Wire.term).length) := by
      apply congrArg Port.input
      apply Fin.ext
      change 1+(i.val-1)=i.val
      omega
    change (BoxPullWeakening.ReverseComponents.tensorJoin (activeOccurrence P A R) (continuation P A R) (active_disjoint P A R)).ports (.input _) = _
    rw [← eq,Occurrence.tensorJoin_right,continuation_input]
    exact congrArg Port.input (Fin.ext (by dsimp [j]; omega))

theorem output (i : Fin O.length) : (occurrence P A R).ports (.output i) = .output i := by
  have eq : (BoxPullWeakening.ReverseComponents.tensorRight A (Serial.net P R)).ports (.output i) = .output i :=
    congrArg Port.output (Fin.ext (Nat.zero_add _))
  change (BoxPullWeakening.ReverseComponents.tensorJoin (activeOccurrence P A R) (continuation P A R) (active_disjoint P A R)).ports (.output i) = _
  rw [← eq,Occurrence.tensorJoin_right,continuation,Occurrence.SerialJoin.occurrence_output]
  exact remainder_output P A R i

theorem cover : Function.Surjective (occurrence P A R).edges := by
  cases d
  all_goals
    rintro ⟨part,e⟩
    cases part
    · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
    · obtain ⟨part,e⟩ := e
      cases part
      · exact ⟨⟨false,e⟩,rfl⟩
      · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Literal reassembly into the returned numeral and the remaining family
followed by the original weakened tree/private cell. -/
noncomputable def iso : DeepIso (target P A R) (source P A R) :=
  (occurrence P A R).iso_of_edge_surjective (input P A R) (output P A R) (cover P A R)

end Hypernets.Copying.Parametricity.TailPrecompose.TensorResult
