import Hypernets.Copying.ContractionTreeGraftWitness
import Hypernets.Copying.ContractionTreeGraftOccurrence
import Hypernets.Copying.CopyingDoubleSymmetry
import Hypernets.Copying.ParametricityClosedCopyPair

/-! The residual-input context for growing a Figure 20 abstraction family.
The new active abstraction remains input zero. Every remaining upstream input
keeps its original order, before the untouched family inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyContext
open Graph Opening

def forwardIndex (a b : Nat) (i : Fin (a+(b+1))) : Fin (a+(b+1)) :=
  ⟨if i.val < a then i.val+1 else if i.val = a then 0 else i.val,by
    have := i.isLt; split <;> (try split) <;> omega⟩
def backwardIndex (a b : Nat) (i : Fin (a+(b+1))) : Fin (a+(b+1)) :=
  ⟨if i.val = 0 then a else if i.val ≤ a then i.val-1 else i.val,by
    have := i.isLt; split <;> (try split) <;> omega⟩

def rotation (a b : Nat) : TypedPermutation (List.replicate (a+(b+1)) .term) where
  bijection :=
    { toFun i := ⟨(forwardIndex a b ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩
      invFun i := ⟨(backwardIndex a b ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩
      left_inv i := by
        apply Fin.ext
        dsimp [forwardIndex,backwardIndex]
        repeat first | split | omega
      right_inv i := by
        apply Fin.ext
        dsimp [forwardIndex,backwardIndex]
        repeat first | split | omega }
  typed i := by
    change (List.replicate (a+(b+1)) Wire.term)[(forwardIndex a b ⟨i.val,by simpa using i.isLt⟩).val] = (List.replicate (a+(b+1)) Wire.term)[i.val]
    simp only [List.getElem_replicate]

variable {d a b : Nat} {O : List Wire}
    (P : Hypernet d (List.replicate a .term) [.term])
    (G : Hypernet d (List.replicate ((b+1)+1) .term) O)

def net : Hypernet d (List.replicate (a+(b+1)) .term) O :=
  CopyingInputPermutation.net (ContractionTree.Graft.net (s := .term) (b := b+1) P G 1) (rotation a b)

noncomputable def upstream : Occurrence P (net P G) :=
  (ContractionTree.Graft.leftOccurrence (s := .term) (b := b+1) P G 1).comp
    (CopyingDouble.Symmetry.forward _ (rotation a b))
noncomputable def family : Occurrence G (net P G) :=
  (ContractionTree.Graft.rightOccurrence (s := .term) (b := b+1) P G 1).comp
    (CopyingDouble.Symmetry.forward _ (rotation a b))

theorem upstream_input (i : Fin (List.replicate a Wire.term).length) :
    (upstream P G).ports (.input i) = .input ⟨i.val+1,by
      have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  dsimp only [upstream,family,Occurrence.comp,Function.comp_apply,CopyingDouble.Symmetry.forward]
  simp only [ContractionTree.Graft.leftOccurrence_ports]
  change (CopyingInputPermutation.ports _ (rotation a b)).toFun
    (ContractionTree.Graft.leftInsert (s := .term) (b := b+1) P G 1 (.input i)) = _
  rw [ContractionTree.Graft.left_input]
  simp only [CopyingInputPermutation.ports,rotation,forwardIndex]
  have small : i.val < a := by simpa using i.isLt
  simp only [small,↓reduceIte]

theorem active_input : (family P G).ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp <;> omega⟩ := by
  dsimp only [upstream,family,Occurrence.comp,Function.comp_apply,CopyingDouble.Symmetry.forward]
  simp only [ContractionTree.Graft.rightOccurrence_ports]
  change (CopyingInputPermutation.ports _ (rotation a b)).toFun
    (ContractionTree.Graft.rightInsert (s := .term) (b := b+1) P G 1 (.input ⟨0,by simp⟩)) = _
  rw [ContractionTree.Graft.right_input]
  simp [ContractionTree.Graft.downstream,CopyingInputPermutation.ports,
    rotation,forwardIndex,Port.map]

theorem retained_input : (family P G).ports (.input ⟨1,by simp⟩) =
    (upstream P G).ports (.output 0) := by
  dsimp only [upstream,family,Occurrence.comp,Function.comp_apply,CopyingDouble.Symmetry.forward]
  simp only [ContractionTree.Graft.leftOccurrence_ports,ContractionTree.Graft.rightOccurrence_ports]
  change (CopyingInputPermutation.ports _ (rotation a b)).toFun
    (ContractionTree.Graft.rightInsert (s := .term) (b := b+1) P G 1 (.input ⟨1,by simp⟩)) =
      (CopyingInputPermutation.ports _ (rotation a b)).toFun
        (ContractionTree.Graft.leftInsert (s := .term) (b := b+1) P G 1 (.output 0))
  apply congrArg
  simpa only [Fin.val_one] using ContractionTree.Graft.selected_input (s := .term) (b := b+1) P G (1 : Fin (b+1+1))

theorem remaining_input (i : Fin b) :
    (family P G).ports (.input ⟨i.val+2,by simp <;> omega⟩) =
      .input ⟨a+i.val+1,by simp <;> omega⟩ := by
  dsimp only [upstream,family,Occurrence.comp,Function.comp_apply,CopyingDouble.Symmetry.forward]
  simp only [ContractionTree.Graft.rightOccurrence_ports]
  change (CopyingInputPermutation.ports _ (rotation a b)).toFun
    (ContractionTree.Graft.rightInsert (s := .term) (b := b+1) P G 1 (.input ⟨i.val+2,by simp <;> omega⟩)) = _
  rw [ContractionTree.Graft.right_input]
  have different : (⟨i.val+2,by omega⟩ : Fin (b+1+1)) ≠ 1 := by
    intro eq; have := congrArg Fin.val eq; simp only [Fin.val_one] at this; omega
  simp only [ContractionTree.Graft.downstream,different,↓reduceDIte]
  have later : ¬ i.val+2 < (1 : Fin (b+1+1)).val := by simp <;> omega
  simp only [later,↓reduceIte,Port.map,CopyingInputPermutation.ports,rotation,forwardIndex]
  apply congrArg Port.input
  apply Fin.ext
  dsimp only [Fin.val_mk,Fin.val_one]
  split <;> (try split) <;> omega

theorem family_output (i : Fin O.length) : (family P G).ports (.output i) = .output i := by
  dsimp only [upstream,family,Occurrence.comp,Function.comp_apply,CopyingDouble.Symmetry.forward]
  simp only [ContractionTree.Graft.rightOccurrence_ports]
  change (CopyingInputPermutation.ports _ (rotation a b)).toFun
    (ContractionTree.Graft.rightInsert (s := .term) (b := b+1) P G 1 (.output i)) = _
  rw [ContractionTree.Graft.right_output]
  rfl

/-- One original enlarged-family specimen is inserted once. The residual
sharing tree is retained identically, without an assumed composition law. -/
noncomputable def witness {T : PreTemplate} (free : FocusFree P)
    {G H : Hypernet d (List.replicate ((b+1)+1) .term) O}
    (w : FillingWitness T G H) : FillingWitness T (net P G) (net P H) :=
  (ContractionTree.Graft.witness (s := .term) (b := b+1) (FillingWitness.refl P free) w 1).inputPermuted (rotation a b)

end Hypernets.Copying.Parametricity.CopyContext
