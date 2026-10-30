import Hypernets.Copying.CopyingMerge
import Hypernets.Copying.CopyingDoubleResources
import Hypernets.Copying.CopyingNestedRowOccurrence

/-! Every original resource row and branch of a binary merge has its complete
original occurrence and exact ordered attachments. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge
open Graph Opening
variable {d a b k h : Nat}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))

theorem pair_output (side : Bool) (i : CopyingDouble.Frame.Resource k h) :
    (pairComponent A B side).ports (.output (by cases side <;> exact i)) =
      .output (CopyRule.copyOutput k h side i) := by
  cases side <;> exact congrArg Port.output (Fin.ext rfl)

noncomputable def resource (i : CopyingDouble.Frame.Resource k h) :
    Occurrence (CanonicalTree.atDepth (CopyingDouble.Frame.sort k h i) 2 d) (net A B) :=
  (CopyingDouble.Components.resource i).comp (Occurrence.serialRight _ _)

theorem resource_input (i : CopyingDouble.Frame.Resource k h) (side : Bool) :
    (resource A B i).ports (.input (if side then ⟨1,by simp⟩ else ⟨0,by simp⟩)) =
      (component A B side).ports (.output (by cases side <;> exact i)) := by
  change BoundarySerial.rightInsert _ _ ((CopyingDouble.Components.resource i).ports (.input _)) =
    BoundarySerial.leftInsert _ _ ((pairComponent A B side).ports (.output _))
  rw [CopyingDouble.Components.resource_input,pair_output,
    CopyRule.serial_right_input,CopyRule.serial_left_output]

theorem resource_output (i : CopyingDouble.Frame.Resource k h) :
    (resource A B i).ports (.output 0) = .output i := by
  change BoundarySerial.rightInsert _ _ ((CopyingDouble.Components.resource i).ports (.output 0)) = _
  rw [CopyingDouble.Components.resource_output,Application.right_serial_output]

theorem resource_disjoint (i j : CopyingDouble.Frame.Resource k h) (different : i ≠ j) :
    ∀ e f, (resource A B i).edges e ≠ (resource A B j).edges f := by
  intro e f eq
  exact CopyingDouble.Components.resource_disjoint i j different e f
    ((Occurrence.serialRight _ _).edge_injective eq)

theorem component_resource_disjoint (side : Bool) (i : CopyingDouble.Frame.Resource k h) :
    ∀ e f, (component A B side).edges e ≠ (resource A B i).edges f := by
  cases d <;> intro e f eq <;> cases eq

theorem components_disjoint : ∀ e f, (component A B false).edges e ≠ (component A B true).edges f := by
  cases d <;> intro e f eq <;> cases eq

end Hypernets.Copying.CopyingMerge
