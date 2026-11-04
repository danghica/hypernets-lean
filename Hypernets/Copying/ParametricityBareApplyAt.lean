import Hypernets.Copying.ParametricityBareApplyJoin
import Hypernets.Copying.ParametricitySelectedFamily
import Hypernets.Copying.BoundaryOccurrence
import Hypernets.Copying.CopyingInputPermutation

/-! Select any original family input without changing its graph carriers.
The selected input is connected to the application; all other family inputs
keep their relative order. The callback remains the sole external output. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyAt
open Graph Opening
variable {n : Nat}

def order (j : Fin (n+1)) : TypedPermutation (List.replicate (n+1) .term) where
  bijection := {
    toFun i := ⟨((FamilyLiteral.front j).toFun ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩
    invFun i := ⟨((FamilyLiteral.front j).invFun ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩
    left_inv i := by
      apply Fin.ext
      change ((FamilyLiteral.front j).invFun ((FamilyLiteral.front j).toFun ⟨i.val,by simpa using i.isLt⟩)).val = i.val
      exact congrArg (fun x : Fin (n+1) => x.val) ((FamilyLiteral.front j).left_inv ⟨i.val,by simpa using i.isLt⟩)
    right_inv i := by
      apply Fin.ext
      change ((FamilyLiteral.front j).toFun ((FamilyLiteral.front j).invFun ⟨i.val,by simpa using i.isLt⟩)).val = i.val
      exact congrArg (fun x : Fin (n+1) => x.val) ((FamilyLiteral.front j).right_inv ⟨i.val,by simpa using i.isLt⟩) }
  typed i := by simp

theorem order_zero (j : Fin (n+1)) : (order j).bijection.toFun ⟨0,by simp⟩ = ⟨j.val,by simp⟩ := rfl

theorem order_rest (j : Fin (n+1)) (i : Fin n) :
    ((order j).bijection.toFun ⟨i.val+1,by simp⟩).val =
      if i.val<j.val then i.val else i.val+1 :=
  FamilyLiteral.front_rest j i

theorem order_selected (j : Fin (n+1)) : (order j).bijection.invFun ⟨j.val,by simp⟩ = ⟨0,by simp⟩ :=
  (order j).bijection.left_inv ⟨0,by simp⟩

variable {d : Nat} (G : Hypernet d (List.replicate (n+1) .term) []) (j : Fin (n+1))

/-- Only original boundary occurrences are reordered; every original family
edge and internal vertex is retained literally. -/
def selected := CopyingInputPermutation.net G (order j).symm

def net := BareApplyFirst.net (selected G j)

noncomputable def head : Occurrence (primitiveNet d (.operation .app)) (net G j) :=
  BareApplyFirst.head (selected G j)

noncomputable def family : Occurrence G (net G j) :=
  (Occurrence.ofBoundaryIso (CopyingInputPermutation.iso G (order j).symm)).comp
    (BareApplyFirst.family (selected G j))

theorem head_input : (head G j).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ :=
  BareApplyFirst.head_input _

theorem head_argument : (head G j).ports (.output (1 : Fin 2)) = .output 0 :=
  BareApplyFirst.head_argument _

theorem family_port (i : Fin (List.replicate (n+1) Wire.term).length) :
    (family G j).ports (.input i) =
      (BareApplyFirst.family (selected G j)).ports (.input ((order j).bijection.invFun i)) := rfl

theorem head_function : (head G j).ports (.output (0 : Fin 2)) =
    (family G j).ports (.input ⟨j.val,by simp⟩) := by
  rw [family_port,order_selected]
  exact BareApplyFirst.head_function _

/-- Canonical remaining positions denote the original inputs in their
original relative order, with precisely the selected member removed. -/
theorem family_remaining (i : Fin n) :
    (family G j).ports (.input ((order j).bijection.toFun ⟨i.val+1,by simp⟩)) =
      .input ⟨i.val+1,by simp⟩ := by
  rw [family_port,(order j).bijection.left_inv]
  exact BareApplyFirst.family_succ _ i

/-- Every unselected original family input is still an external input;
its position is exactly its index after deleting the selected member. -/
theorem family_unselected (i : Fin (List.replicate (n+1) Wire.term).length)
    (different : i ≠ ⟨j.val,by simp⟩) :
    (family G j).ports (.input i) = .input ((order j).bijection.invFun i) := by
  have nonzero : ((order j).bijection.invFun i).val ≠ 0 := by
    intro eq
    have z : (order j).bijection.invFun i = ⟨0,by simp⟩ := Fin.ext eq
    have back := (order j).bijection.right_inv i
    rw [z,order_zero] at back
    exact different back.symm
  let r : Fin n := ⟨((order j).bijection.invFun i).val-1,by
    have h := ((order j).bijection.invFun i).isLt
    simp only [List.length_replicate] at h
    omega⟩
  have eq : (order j).bijection.invFun i = ⟨r.val+1,by simp⟩ := Fin.ext (by dsimp [r];omega)
  rw [family_port,eq]
  exact BareApplyFirst.family_succ _ r

end Hypernets.Copying.Parametricity.BareApplyAt
