import Hypernets.Copying.ContractionTreeGraftOccurrence
import Hypernets.Copying.TensorOccurrencePorts
import Hypernets.Copying.OccurrenceCoverIso

/-! Move an actual complete two-input resource row from a selected family
branch into the private sharing component. No row edge is simplified. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.TensorGraft
open Graph Opening
variable {d b : Nat} {I J O : List Wire}
    (X : Hypernet d I (List.replicate 2 .term))
    (D : Hypernet d (List.replicate 2 .term) [.term])
    (R : Hypernet d J (List.replicate b .term))
    (C : Hypernet d (.term :: List.replicate b .term) O)

def source : Hypernet d (I++J) O := Serial.net (Net.Tensor.net (Serial.net X D) R) C

def tail : Hypernet d (List.replicate (b+1) .term) O :=
  C.reboundary (by simp [List.replicate_succ]) rfl

def unmerged : Hypernet d (I++J) (List.replicate (2+b) .term) :=
  (Net.Tensor.net X R).reboundary rfl (by rw [List.replicate_append_replicate])

def target : Hypernet d (I++J) O :=
  Serial.net (unmerged X R) (ContractionTree.Graft.net (s := .term) D (tail C) ⟨0,by omega⟩)

noncomputable def block := BoxPullWeakening.ReverseComponents.serialLeft
  (Net.Tensor.net (Serial.net X D) R) C
noncomputable def firstBlock := (BoxPullWeakening.ReverseComponents.tensorLeft (Serial.net X D) R).comp (block X D R C)
noncomputable def x := (BoxPullWeakening.ReverseComponents.serialLeft X D).comp (firstBlock X D R C)
noncomputable def row := (BoxPullWeakening.ReverseComponents.serialRight X D).comp (firstBlock X D R C)
noncomputable def rest := (BoxPullWeakening.ReverseComponents.tensorRight (Serial.net X D) R).comp (block X D R C)
noncomputable def continuation : Occurrence (tail C) (source X D R C) := (BoxPullWeakening.ReverseComponents.serialRight
  (Net.Tensor.net (Serial.net X D) R) C).reboundarySource (by simp [List.replicate_succ]) rfl

theorem selected_link : (row X D R C).ports (.output (0 : Fin 1)) =
    (continuation X D R C).ports (.input ⟨0,by simp⟩) := by
  cases d <;> rfl

theorem row_continuation_disjoint : ∀ e f,
    (row X D R C).edges e ≠ (continuation X D R C).edges f := by
  cases d <;> intro e f eq <;> cases eq

noncomputable def grafted := ContractionTree.Graft.Join.occurrence (s := .term)
  (row X D R C) (continuation X D R C) ⟨0,by omega⟩ (selected_link X D R C)
    (row_continuation_disjoint X D R C)

theorem x_rest_disjoint : ∀ e f, (x X D R C).edges e ≠ (rest X D R C).edges f := by
  cases d <;> intro e f eq <;> cases eq

noncomputable def pair := BoxPullWeakening.ReverseComponents.tensorJoin
  (x X D R C) (rest X D R C) (x_rest_disjoint X D R C)
noncomputable def unmergedOccurrence : Occurrence (unmerged X R) (source X D R C) :=
  (pair X D R C).reboundarySource rfl (by rw [List.replicate_append_replicate])

theorem x_row_link (i : Fin (List.replicate 2 Wire.term).length) :
    (x X D R C).ports (.output i) = (row X D R C).ports (.input i) := by
  cases d <;> rfl

theorem rest_continuation_link (i : Fin (List.replicate b Wire.term).length) :
    (rest X D R C).ports (.output i) = (continuation X D R C).ports
      (.input ⟨i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  cases d
  all_goals
    calc
      _ = (BoxPullWeakening.ReverseComponents.serialLeft (Net.Tensor.net (Serial.net X D) R) C).ports
          (.output ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) := by
        dsimp only [rest,block,Occurrence.comp,Function.comp_apply]
        apply congrArg (BoxPullWeakening.ReverseComponents.serialLeft (Net.Tensor.net (Serial.net X D) R) C).ports
        exact congrArg Port.output (Fin.ext rfl)
      _ = (BoxPullWeakening.ReverseComponents.serialRight (Net.Tensor.net (Serial.net X D) R) C).ports
          (.input ⟨1+i.val,by have := i.isLt; simp at *; omega⟩) :=
        BoxPullWeakening.ReverseComponents.serial_boundary _ _ _
      _ = _ := by
        change (BoxPullWeakening.ReverseComponents.serialRight (Net.Tensor.net (Serial.net X D) R) C).ports (.input _) =
          (BoxPullWeakening.ReverseComponents.serialRight (Net.Tensor.net (Serial.net X D) R) C).ports (.input _)
        apply congrArg (BoxPullWeakening.ReverseComponents.serialRight (Net.Tensor.net (Serial.net X D) R) C).ports
        apply congrArg Port.input
        exact Fin.ext (by simp; omega)

theorem pair_left_output (i : Fin (List.replicate 2 Wire.term).length) :
    (unmergedOccurrence X D R C).ports (.output ⟨i.val,by have := i.isLt; simp at *; omega⟩) =
      (x X D R C).ports (.output i) := by
  have eq := Occurrence.tensorJoin_left (x X D R C) (rest X D R C) (x_rest_disjoint X D R C) (.output i)
  exact eq

theorem pair_right_output (i : Fin (List.replicate b Wire.term).length) :
    (unmergedOccurrence X D R C).ports (.output ⟨2+i.val,by have := i.isLt; simp at *; omega⟩) =
      (rest X D R C).ports (.output i) := by
  have eq := Occurrence.tensorJoin_right (x X D R C) (rest X D R C) (x_rest_disjoint X D R C) (.output i)
  exact eq

theorem graft_left_input (i : Fin (List.replicate 2 Wire.term).length) :
    (grafted X D R C).ports (.input ⟨i.val,by have := i.isLt; simp at *; omega⟩) =
      (row X D R C).ports (.input i) := by
  have eq := ContractionTree.Graft.Join.left_port (s := .term) (a := 2) (b := b) (row X D R C) (continuation X D R C)
    ⟨0,by omega⟩ (selected_link X D R C) (row_continuation_disjoint X D R C) (.input i)
  rw [ContractionTree.Graft.left_input] at eq
  exact eq

theorem graft_right_input (i : Fin (List.replicate b Wire.term).length) :
    (grafted X D R C).ports (.input ⟨2+i.val,by have := i.isLt; simp at *; omega⟩) =
      (continuation X D R C).ports (.input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩) := by
  let j : Fin (List.replicate (b+1) Wire.term).length := ⟨i.val+1,by have := i.isLt; simp at *; omega⟩
  have eq := ContractionTree.Graft.Join.right_port (s := .term) (a := 2) (b := b) (row X D R C) (continuation X D R C)
    ⟨0,by omega⟩ (selected_link X D R C) (row_continuation_disjoint X D R C) (.input j)
  rw [ContractionTree.Graft.right_input] at eq
  simp only [ContractionTree.Graft.downstream] at eq
  have choices : ∀ h h0, (⟨i.val+1,h⟩ : Fin (b+1)) ≠ ⟨0,h0⟩ := by
    intro h h0 bad
    have val := congrArg Fin.val bad
    change i.val+1 = 0 at val
    omega
  simpa only [grafted,j,choices,↓reduceDIte,Fin.val_mk,Nat.not_lt_zero,↓reduceIte,Nat.add_sub_cancel,Port.map] using eq

theorem boundary : ∀ i, (unmergedOccurrence X D R C).ports (.output i) = (grafted X D R C).ports (.input i) := by
  intro i
  have bound : i.val < 2+b := by simpa only [List.length_replicate] using i.isLt
  by_cases first : i.val < 2
  · let j : Fin (List.replicate 2 Wire.term).length := ⟨i.val,by simpa⟩
    have index : i = ⟨j.val,by have := i.isLt; exact this⟩ := Fin.ext rfl
    rw [index,pair_left_output,graft_left_input]
    exact x_row_link X D R C j
  · let j : Fin (List.replicate b Wire.term).length := ⟨i.val-2,by simpa only [List.length_replicate] using (show i.val-2 < b by omega)⟩
    have index : i = ⟨2+j.val,by
      have jb : j.val < b := by simpa only [List.length_replicate] using j.isLt
      simpa only [List.length_replicate] using Nat.add_lt_add_left jb 2⟩ := Fin.ext (by dsimp [j]; omega)
    rw [index,pair_right_output,graft_right_input]
    exact rest_continuation_link X D R C j

theorem pair_graft_disjoint : ∀ e f,
    (unmergedOccurrence X D R C).edges e ≠ (grafted X D R C).edges f := by
  cases d
  all_goals
    rintro ⟨side,e⟩ ⟨part,f⟩ eq
    cases side <;> cases part <;> cases eq

noncomputable def occurrence : Occurrence (target X D R C) (source X D R C) :=
  Occurrence.SerialJoin.occurrence (unmergedOccurrence X D R C) (grafted X D R C)
    (boundary X D R C) (pair_graft_disjoint X D R C)

theorem x_input (i : Fin I.length) :
    (x X D R C).ports (.input i) = .input (Net.Tensor.join I J ⟨false,i⟩) := by
  cases d
  all_goals
    change BoundarySerial.leftInsert (Net.Tensor.net (Serial.net X D) R) C
      (Net.Parallel.embed (Net.Tensor.family (Serial.net X D) R)
        (Net.Tensor.boundary _ _ _ _) false (BoundarySerial.leftInsert X D (.input i))) = _
    rw [Combined.left_input]
    change BoundarySerial.leftInsert _ C (.input (Net.Tensor.join I J ⟨false,i⟩)) = _
    exact Combined.left_input _ _ _

theorem rest_input (i : Fin J.length) :
    (rest X D R C).ports (.input i) = .input (Net.Tensor.join I J ⟨true,i⟩) := by
  cases d
  all_goals
    change BoundarySerial.leftInsert _ C (.input (Net.Tensor.join I J ⟨true,i⟩)) = _
    exact Combined.left_input _ _ _

theorem input (i : Fin (I++J).length) : (occurrence X D R C).ports (.input i) = .input i := by
  rw [occurrence,Occurrence.SerialJoin.occurrence_input]
  change (pair X D R C).ports (.input i) = .input i
  have index := Net.Tensor.join_split I J i
  generalize choice : Net.Tensor.split I J i = q at index
  rcases q with ⟨side,j⟩
  rw [← index]
  cases side
  · have eq := Occurrence.tensorJoin_left (x X D R C) (rest X D R C) (x_rest_disjoint X D R C) (.input j)
    exact eq.trans (x_input X D R C j)
  · have eq := Occurrence.tensorJoin_right (x X D R C) (rest X D R C) (x_rest_disjoint X D R C) (.input j)
    exact eq.trans (rest_input X D R C j)

theorem output (i : Fin O.length) : (occurrence X D R C).ports (.output i) = .output i := by
  rw [occurrence,Occurrence.SerialJoin.occurrence_output]
  have eq := ContractionTree.Graft.Join.right_port (s := .term) (a := 2) (b := b)
    (row X D R C) (continuation X D R C) ⟨0,by omega⟩ (selected_link X D R C)
    (row_continuation_disjoint X D R C) (.output i)
  rw [ContractionTree.Graft.right_output] at eq
  change (grafted X D R C).ports (.output i) = _ at eq
  rw [eq]
  change BoundarySerial.rightInsert _ C (.output i) = .output i
  exact Application.right_serial_output _ _ i

theorem cover : Function.Surjective (occurrence X D R C).edges := by
  cases d
  all_goals
    rintro ⟨outer,e⟩
    cases outer
    · rcases e with ⟨side,e⟩
      cases side
      · rcases e with ⟨part,e⟩
        cases part
        · exact ⟨⟨false,⟨false,e⟩⟩,rfl⟩
        · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
      · exact ⟨⟨false,⟨true,e⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- The entire actual two-input resource row moves into the private sharing
component, preserving every original vertex attachment and external order. -/
noncomputable def iso : DeepIso (target X D R C) (source X D R C) :=
  (occurrence X D R C).iso_of_edge_surjective (input X D R C) (output X D R C) (cover X D R C)

end Hypernets.Copying.Parametricity.TensorGraft
