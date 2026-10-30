import Hypernets.Copying.CopyingDoubleComponents

/-! Combine two actual graph branches through the unchanged Figure 17
resource distributors. Both ordered term-input blocks are retained, including
empty residual-tree branches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge
open Graph Opening

/-- Parallel input concatenation and the original variable/atom output blocks. -/
def boundary (a b k h : Nat) :
    Net.Parallel.Boundary
      (Net.Tensor.interfaces (List.replicate a Wire.term) (List.replicate b Wire.term))
      (Net.Tensor.interfaces (environmentInterface k h) (environmentInterface k h))
      (List.replicate a Wire.term ++ List.replicate b Wire.term)
      ((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
        (List.replicate h Wire.atom ++ List.replicate h Wire.atom)) where
  inputs := Net.Tensor.ports _ _
  outputs := (Translation.pairBoundary k h).outputs
  input_label := Net.Tensor.join_label _ _
  output_label := (Translation.pairBoundary k h).output_label

/-- The literal pair before its unchanged external resource distributors. -/
def pair {d a b k h}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h)) :
    Hypernet d (List.replicate (a+b) .term) (environmentInterface (k*2) (h*2)) :=
  (Net.Parallel.net (Net.Tensor.family A B) (boundary a b k h)
      ⟨[false,true],by intro side; cases side <;> simp⟩).reboundary
    (by simp [List.replicate_append_replicate]) (by simp [environmentInterface,Nat.mul_two])

/-- Merge the two resource copies using the full canonical D1,2 row for every
variable and atom, keeping the first branch's inputs before the second's. -/
def net {d a b k h}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h)) :
    Hypernet d (List.replicate (a+b) .term) (environmentInterface k h) :=
  Serial.net (pair A B) (Translation.environmentDistributor d k h 2)

variable {d a b k h : Nat}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))

/-- Each branch is its actual complete-label occurrence in the merged graph. -/
def pairComponent (side : Bool) : Occurrence (Net.Tensor.family A B side) (pair A B) where
  ports v := Port.cast (by simp [List.replicate_append_replicate]) (by simp [environmentInterface,Nat.mul_two])
    (Net.Parallel.embed (Net.Tensor.family A B) (boundary a b k h) side v)
  internals v := ⟨side,v⟩
  edges e := ⟨side,e⟩
  internal_map _ := rfl
  internal_injective := by intro x y eq; exact eq_of_heq (Sigma.mk.inj eq).2
  edge_injective := by intro x y eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source e := by
    change ((Net.Tensor.family A B side).source e).map _ = (((Net.Tensor.family A B side).source e).map _).map _
    rw [List.map_map]; rfl
  target e := by
    change ((Net.Tensor.family A B side).target e).map _ = (((Net.Tensor.family A B side).target e).map _).map _
    rw [List.map_map]; rfl

noncomputable def component (side : Bool) : Occurrence (Net.Tensor.family A B side) (net A B) :=
  (pairComponent A B side).comp (BoxPullWeakening.ReverseComponents.serialLeft _ _)

theorem left_input (i : Fin (List.replicate a Wire.term).length) :
    (component A B false).ports (.input i) =
      .input ⟨i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  change BoundarySerial.leftInsert _ _ ((pairComponent A B false).ports (.input i)) = _
  have eq : (pairComponent A B false).ports (.input i) =
      Port.input (⟨i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ : Fin (List.replicate (a+b) Wire.term).length) := by
    exact congrArg Port.input (Fin.ext rfl)
  rw [eq,Combined.left_input]

theorem right_input (i : Fin (List.replicate b Wire.term).length) :
    (component A B true).ports (.input i) =
      .input ⟨a+i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  change BoundarySerial.leftInsert _ _ ((pairComponent A B true).ports (.input i)) = _
  have eq : (pairComponent A B true).ports (.input i) =
      Port.input (⟨a+i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ : Fin (List.replicate (a+b) Wire.term).length) := by
    apply congrArg Port.input
    apply Fin.ext
    change (List.replicate a Wire.term).length+i.val = a+i.val
    simp only [List.length_replicate]
  rw [eq,Combined.left_input]

end Hypernets.Copying.CopyingMerge
