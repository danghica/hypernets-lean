import Hypernets.Copying.CopyingMergeResources
import Hypernets.Copying.CopyingMergeNormal
import Hypernets.Copying.OccurrenceBoundaryTarget

/-! Full original branch and resource occurrences in both associations of
binary merging. All external inputs are ordered A, then B, then C. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge.Components
open Graph Opening
variable {d a b c k h : Nat}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))
    (C : Hypernet d (List.replicate c .term) (environmentInterface k h))

def target (associateRight : Bool) : Hypernet d (List.replicate (a+b+c) .term) (environmentInterface k h) :=
  if associateRight then (net A (net B C)).reboundary (by congr 1; omega) rfl else net (net A B) C

noncomputable def branch (associateRight : Bool) (tag : Fin 3) :
    Occurrence (branches A B C tag) (target A B C associateRight) :=
  match associateRight,tag with
  | false,⟨0,_⟩ => (component A B false).comp (component (net A B) C false)
  | false,⟨1,_⟩ => (component A B true).comp (component (net A B) C false)
  | false,⟨2,_⟩ => component (net A B) C true
  | true,⟨0,_⟩ => (component A (net B C) false).reboundaryTarget (by congr 1; omega) rfl
  | true,⟨1,_⟩ => ((component B C false).comp (component A (net B C) true)).reboundaryTarget (by congr 1; omega) rfl
  | true,⟨2,_⟩ => ((component B C true).comp (component A (net B C) true)).reboundaryTarget (by congr 1; omega) rfl
  | _,⟨n+3,bound⟩ => False.elim (by omega)

noncomputable def innerRow (associateRight : Bool) (i : Frame.Resource k h) :
    Occurrence (CanonicalTree.atDepth (CopyingDouble.Frame.sort k h i) 2 d) (target A B C associateRight) := by
  cases associateRight
  · exact (resource A B i).comp (component (net A B) C false)
  · exact ((resource B C i).comp (component A (net B C) true)).reboundaryTarget (by congr 1; omega) rfl

noncomputable def outerRow (associateRight : Bool) (i : Frame.Resource k h) :
    Occurrence (CanonicalTree.atDepth (CopyingDouble.Frame.sort k h i) 2 d) (target A B C associateRight) := by
  cases associateRight
  · exact resource (net A B) C i
  · exact (resource A (net B C) i).reboundaryTarget (by congr 1; omega) rfl

theorem row_link (r : Bool) (i : Frame.Resource k h) :
    (innerRow A B C r i).ports (.output 0) =
      (outerRow A B C r i).ports (.input (if r then ⟨1,by simp⟩ else ⟨0,by simp⟩)) := by
  cases r
  · change (component (net A B) C false).ports ((resource A B i).ports (.output 0)) = _
    rw [resource_output]
    exact (resource_input (net A B) C i false).symm
  · change Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl ((component A (net B C) true).ports ((resource B C i).ports (.output 0))) = _
    rw [resource_output]
    exact congrArg (Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl) (resource_input A (net B C) i true).symm

theorem row_disjoint (r : Bool) (i : Frame.Resource k h) :
    ∀ e f, (innerRow A B C r i).edges e ≠ (outerRow A B C r i).edges f := by
  cases r <;> cases d <;> intro e f eq <;> cases eq

noncomputable def row (r : Bool) (i : Frame.Resource k h) :
    Occurrence (Frame.row (d := d) i r) (target A B C r) :=
  (CopyingNested.Row.occurrence (innerRow A B C r i) (outerRow A B C r i) r
    (row_link A B C r i) (row_disjoint A B C r i)).reboundarySource
      (congrArg (List.replicate 3) (CopyingDouble.Frame.sort_wire k h i))
      (congrArg List.singleton (CopyingDouble.Frame.sort_wire k h i))

theorem row_inner_edge (r : Bool) (i : Frame.Resource k h)
    (e : (CanonicalTree.atDepth (CopyingDouble.Frame.sort k h i) 2 d).Edge) :
    (row A B C r i).edges ⟨false,(by cases d <;> exact e)⟩ = (innerRow A B C r i).edges e := by
  cases d <;> rfl

theorem row_outer_edge (r : Bool) (i : Frame.Resource k h)
    (e : (CanonicalTree.atDepth (CopyingDouble.Frame.sort k h i) 2 d).Edge) :
    (row A B C r i).edges ⟨true,(by cases d <;> exact e)⟩ = (outerRow A B C r i).edges e := by
  cases d <;> rfl

theorem branch_input (r : Bool) (tag : Fin 3)
    (i : Fin (List.replicate (Inputs.arity a b c tag) Wire.term).length) :
    (branch A B C r tag).ports (.input i) =
      .input ⟨Inputs.offset a b tag+i.val,by
        have := i.isLt
        rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
        all_goals simp [Inputs.arity,Inputs.offset] at *; omega⟩ := by
  cases r
  all_goals rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
  · change (component (net A B) C false).ports ((component A B false).ports (.input i)) = _
    rw [left_input,left_input]
    exact congrArg Port.input (Fin.ext (by simp [Inputs.offset]))
  · change (component (net A B) C false).ports ((component A B true).ports (.input i)) = _
    rw [right_input,left_input]
    rfl
  · exact right_input (net A B) C i
  · change Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl ((component A (net B C) false).ports (.input i)) = _
    rw [left_input]
    exact congrArg Port.input (Fin.ext (by simp [Inputs.offset]))
  · change Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl ((component A (net B C) true).ports ((component B C false).ports (.input i))) = _
    rw [left_input,right_input]
    rfl
  · change Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl ((component A (net B C) true).ports ((component B C true).ports (.input i))) = _
    rw [right_input,right_input]
    exact congrArg Port.input (Fin.ext (by simp [Inputs.offset]; omega))

theorem row_input (r : Bool) (i : Frame.Resource k h) (tag : Fin 3) :
    (row A B C r i).ports (.input ⟨tag.val,by simp⟩) =
      (branch A B C r tag).ports (.output i) := by
  cases r
  all_goals rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
  · change (component (net A B) C false).ports ((resource A B i).ports (.input ⟨0,by simp⟩)) = _
    rw [show (resource A B i).ports (.input ⟨0,by simp⟩) = _ from resource_input A B i false]
    rfl
  · change (component (net A B) C false).ports ((resource A B i).ports (.input ⟨1,by simp⟩)) = _
    rw [show (resource A B i).ports (.input ⟨1,by simp⟩) = _ from resource_input A B i true]
    rfl
  · exact resource_input (net A B) C i true
  · exact congrArg (Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl) (resource_input A (net B C) i false)
  · change Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl ((component A (net B C) true).ports ((resource B C i).ports (.input ⟨0,by simp⟩))) = _
    rw [show (resource B C i).ports (.input ⟨0,by simp⟩) = _ from resource_input B C i false]
    rfl
  · change Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl ((component A (net B C) true).ports ((resource B C i).ports (.input ⟨1,by simp⟩))) = _
    rw [show (resource B C i).ports (.input ⟨1,by simp⟩) = _ from resource_input B C i true]
    rfl

theorem row_output (r : Bool) (i : Frame.Resource k h) :
    (row A B C r i).ports (.output 0) = .output i := by
  cases r
  · exact resource_output (net A B) C i
  · exact congrArg (Port.cast (show List.replicate (a+(b+c)) Wire.term = List.replicate (a+b+c) Wire.term by congr 1; omega) rfl) (resource_output A (net B C) i)


theorem branches_disjoint (r : Bool) (tag other : Fin 3) (different : tag ≠ other) :
    ∀ e f, (branch A B C r tag).edges e ≠ (branch A B C r other).edges f := by
  cases r <;> cases d
  all_goals rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
  all_goals rcases CopyingDouble.Frame.triple other with rfl | rfl | rfl
  all_goals intro e f eq
  all_goals first | exact different rfl | cases eq

theorem branch_row_disjoint (r : Bool) (tag : Fin 3) (i : Frame.Resource k h) :
    ∀ e f, (branch A B C r tag).edges e ≠ (row A B C r i).edges f := by
  cases r <;> cases d
  all_goals rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
  all_goals rintro e ⟨side,f⟩ eq
  all_goals cases side <;> cases eq

theorem rows_disjoint (r : Bool) (i j : Frame.Resource k h) (different : i ≠ j) :
    ∀ e f, (row A B C r i).edges e ≠ (row A B C r j).edges f := by
  cases r
  · cases d
    all_goals
      rintro ⟨side,e⟩ ⟨other,f⟩ eq
      cases side <;> cases other
      · exact resource_disjoint A B i j different e f ((component (net A B) C false).edge_injective eq)
      · cases eq
      · cases eq
      · exact resource_disjoint (net A B) C i j different e f eq
  · cases d
    all_goals
      rintro ⟨side,e⟩ ⟨other,f⟩ eq
      cases side <;> cases other
      · exact resource_disjoint B C i j different e f ((component A (net B C) true).edge_injective eq)
      · cases eq
      · cases eq
      · exact resource_disjoint A (net B C) i j different e f eq

end Hypernets.Copying.CopyingMerge.Components
