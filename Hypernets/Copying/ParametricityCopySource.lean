import Hypernets.Copying.ContractionTreeGraftOccurrence
import Hypernets.Copying.OccurrenceTensorBoundary
import Hypernets.Copying.OccurrenceBoundaryTarget
import Hypernets.Copying.OccurrenceCoverIso

/-! Exact isolation of an upstream sharing graph feeding the selected first
abstraction of an arbitrary ordered family. No unused input is discarded. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopySource
open Graph Opening
variable {d a n : Nat} {J K : List Wire}
    (P : Hypernet d (List.replicate a .term) [.term])
    (H : Hypernet d [.term] J) (R : Hypernet d (List.replicate n .term) K)

abbrev target : Hypernet d (List.replicate (a+n) .term) (J++K) :=
  (Net.Tensor.net (Serial.net P H) R).reboundary (by rw [List.replicate_append_replicate]) rfl
abbrev whole : Hypernet d (List.replicate (n+1) .term) (J++K) :=
  (Net.Tensor.net H R).reboundary (by simp [List.replicate_succ]) rfl
noncomputable def left : Occurrence (Serial.net P H) (target P H R) :=
  (BoxPullWeakening.ReverseComponents.tensorLeft _ R).reboundaryTarget _ rfl
noncomputable def right : Occurrence R (target P H R) :=
  (BoxPullWeakening.ReverseComponents.tensorRight _ R).reboundaryTarget _ rfl
noncomputable def upstream : Occurrence P (target P H R) :=
  (BoxPullWeakening.ReverseComponents.serialLeft P H).comp (left P H R)
noncomputable def selected : Occurrence H (target P H R) :=
  (Occurrence.serialRight P H).comp (left P H R)
theorem selected_disjoint : ∀ e f, (selected P H R).edges e ≠ (right P H R).edges f := by
  cases d <;> intro e f eq <;> cases eq
noncomputable def family : Occurrence (whole H R) (target P H R) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected P H R) (right P H R)
    (selected_disjoint P H R)).reboundarySource _ rfl

theorem family_first : (family P H R).ports (.input ⟨0,by simp⟩) = (selected P H R).ports (.input 0) := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P H R) (right P H R) (selected_disjoint P H R)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft H R).ports (.input 0)) = _
  exact Occurrence.tensorJoin_left _ _ _ _
theorem family_rest (i : Fin n) :
    (family P H R).ports (.input ⟨i.val+1,by simp⟩) = .input ⟨a+i.val,by simp <;> omega⟩ := by
  have idx : (⟨i.val+1,by simp⟩ : Fin (List.replicate (n+1) Wire.term).length) = ⟨1+i.val,by simp <;> omega⟩ :=
    Fin.ext (by change i.val+1=1+i.val;omega)
  rw [idx]
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P H R) (right P H R) (selected_disjoint P H R)).ports
    ((BoxPullWeakening.ReverseComponents.tensorRight H R).ports (.input ⟨i.val,by simp⟩)) = _
  rw [Occurrence.tensorJoin_right]
  exact congrArg Port.input (Fin.ext (by change (List.replicate a Wire.term).length+i.val=a+i.val;simp))
theorem link : (upstream P H R).ports (.output 0) = (family P H R).ports (.input ⟨0,by simp⟩) := by
  rw [family_first]
  exact congrArg (left P H R).ports (BoxPullWeakening.ReverseComponents.serial_boundary P H 0)
theorem disjoint : ∀ e f, (upstream P H R).edges e ≠ (family P H R).edges f := by
  cases d <;> intro e f eq
  all_goals
    rcases f with ⟨side,f⟩; cases side
    · have impossible := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases impossible
    · cases eq

noncomputable def occurrence : Occurrence (ContractionTree.Graft.net (s := .term) P (whole H R) 0) (target P H R) :=
  ContractionTree.Graft.Join.occurrence (upstream P H R) (family P H R) 0
    (by simpa only [Fin.val_zero] using link P H R) (disjoint P H R)

theorem input (i : Fin (List.replicate (a+n) Wire.term).length) :
    (occurrence P H R).ports (.input i) = .input i := by
  by_cases before : i.val<a
  · let j : Fin (List.replicate a Wire.term).length := ⟨i.val,by simpa using before⟩
    have eq : ContractionTree.Graft.leftInsert (s := .term) P (whole H R) 0 (.input j) = .input i := by
      rw [ContractionTree.Graft.left_input];rfl
    rw [← eq]
    change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
    rw [ContractionTree.Graft.Join.left_port]
    change (left P H R).ports (BoundarySerial.leftInsert P H (.input j)) = _
    rw [Combined.left_input]
    rfl
  · let j : Fin n := ⟨i.val-a,by have := i.isLt; simp only [List.length_replicate] at this;omega⟩
    have val : a+j.val=i.val := by dsimp [j];omega
    have eq : ContractionTree.Graft.rightInsert (s := .term) P (whole H R) 0
        (.input ⟨j.val+1,by simp⟩) = .input i := by
      rw [ContractionTree.Graft.right_input]
      have ne : (⟨j.val+1,by omega⟩ : Fin (n+1)) ≠ 0 := by
        intro eq; have := congrArg Fin.val eq; simp only [Fin.val_zero] at this;omega
      simp only [ContractionTree.Graft.downstream,ne,↓reduceDIte,Fin.val_zero,Nat.not_lt_zero,
        ↓reduceIte,Nat.add_sub_cancel,Port.map]
      exact congrArg Port.input (Fin.ext val)
    rw [← eq]
    change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
    rw [ContractionTree.Graft.Join.right_port,family_rest]
    exact congrArg Port.input (Fin.ext val)

theorem family_output (i : Fin (J++K).length) : (family P H R).ports (.output i) = .output i := by
  let x := Net.Tensor.split J K i
  have eq := Net.Tensor.join_split J K i
  change Net.Tensor.join J K x=i at eq
  rcases x with ⟨side,j⟩; cases side
  · change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P H R) (right P H R) (selected_disjoint P H R)).ports (.output i) = _
    have represented : (BoxPullWeakening.ReverseComponents.tensorLeft H R).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented,Occurrence.tensorJoin_left]
    change (left P H R).ports (BoundarySerial.rightInsert P H (.output j)) = _
    rw [Application.right_serial_output]
    exact congrArg Port.output eq
  · change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P H R) (right P H R) (selected_disjoint P H R)).ports (.output i) = _
    have represented : (BoxPullWeakening.ReverseComponents.tensorRight H R).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented,Occurrence.tensorJoin_right]
    exact congrArg Port.output eq

theorem output (i : Fin (J++K).length) : (occurrence P H R).ports (.output i) = .output i := by
  rw [← ContractionTree.Graft.right_output (s := .term) P (whole H R) (0 : Fin (n+1)) i]
  change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
  rw [ContractionTree.Graft.Join.right_port,family_output]

theorem cover : Function.Surjective (occurrence P H R).edges := by
  cases d
  all_goals
    rintro ⟨side,e⟩;cases side
    · rcases e with ⟨side,e⟩;cases side
      · exact ⟨⟨false,e⟩,rfl⟩
      · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

noncomputable def iso : DeepIso (ContractionTree.Graft.net (s := .term) P (whole H R) 0) (target P H R) :=
  (occurrence P H R).iso_of_edge_surjective (input P H R) (output P H R) (cover P H R)

end Hypernets.Copying.Parametricity.CopySource
