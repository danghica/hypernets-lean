import Hypernets.Copying.CopyingMergeRetainedIso
import Hypernets.Copying.OccurrenceBoundaryTarget
import Hypernets.Copying.CopyingTemplateRemotePayload

/-! Every original input of a copying reduct still resolves to one complete
original payload. Input zero reaches its active copy immediately; the other
inputs follow the actual weakened residual tree to the retained copy. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRetainedContext
open Graph Opening

/-- Both branches of the original active/retained context, including an
empty retained input interface, occur with their complete recursive labels. -/
noncomputable def branch {d r k h}
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate r .term) (environmentInterface k h)) (side : Bool) :
    Occurrence (Net.Tensor.family H B side) (after H B) :=
  ((CopyingMerge.component (a := 1) H B side).reboundaryTarget (by rw [Nat.add_comm]) rfl).comp
    (Occurrence.ofIso (CopyingMerge.retainedIso H B).symm)

theorem branch_left_input {d r k h}
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate r .term) (environmentInterface k h)) :
    (branch H B false).ports (.input ⟨0,by simp [Net.Tensor.interfaces]⟩) = .input ⟨0,by simp⟩ := by
  change Port.map _ (Port.cast (by rw [Nat.add_comm]) rfl ((CopyingMerge.component (a := 1) H B false).ports (.input ⟨0,by simp [Net.Tensor.interfaces]⟩))) = _
  rw [CopyingMerge.left_input]
  rfl

theorem branch_right_input {d r k h}
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate r .term) (environmentInterface k h))
    (i : Fin (List.replicate r Wire.term).length) :
    (branch H B true).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  change Port.map _ (Port.cast (by rw [Nat.add_comm]) rfl ((CopyingMerge.component (a := 1) H B true).ports (.input i))) = _
  rw [CopyingMerge.right_input]
  exact congrArg Port.input (Fin.ext (by change 1+i.val = i.val+1; omega))

end Hypernets.Copying.CopyingRetainedContext

namespace Hypernets.Copying.CopyingTemplate
open Graph Opening

/-- Every right input resolves to an original complete normalized payload.
The count is allowed to be zero precisely because the distinguished input
already exposes the active payload after the original copying rewrite. -/
theorem Pair.right_input_payload {d I O} {G H : Hypernet d I O}
    (pair : Pair G H) (i : Fin I.length) :
    ∃ k h, ∃ V : Hypernet d [.term] (environmentInterface k h),
      ∃ normal : CopyRule.NormalForm V, FocusFree V ∧
      ∃ payload : Occurrence V H, ∃ m,
        CopyTrace.Resolves H (.input i) (payload.edges normal.head) normal.primitive m := by
  cases pair with
  | witness f literal g =>
    cases literal with
    | @copy n k h tree A copyable free =>
      obtain ⟨V,⟨normal⟩,⟨iso⟩⟩ := CopyRule.normal_form copyable
      let inA := Occurrence.ofIso iso.symm
      have head := inA.matchEmbedding.head normal.head_at
      have kind : CopyTrace.PayloadHead normal.primitive := by
        obtain ⟨e,p,other,kind⟩ := normal.copyable.head_exists
        exact (MatchEmbedding.head_unique normal.head_at other).2 ▸ kind
      have normalizedFree : FocusFree V := (allLabels_iso_iff _ iso).mp free
      by_cases zero : i.val = 0
      · let active := (CopyingRetainedContext.branch A (Serial.net (CopyRule.residual tree d) A) false).comp (Occurrence.ofIso g)
        let payload := inA.comp active
        have resolve : CopyTrace.Resolves A (.input 0) (inA.edges normal.head) normal.primitive 0 :=
          ⟨_,head.2,.refl _,head.1,kind⟩
        have mapped := CopyTrace.resolves_map active.matchEmbedding resolve
        have atInput : active.ports (.input (0 : Fin 1)) = .input i := by
          change Port.map _ ((CopyingRetainedContext.branch A (Serial.net (CopyRule.residual tree d) A) false).ports (.input ⟨0,by simp [Net.Tensor.interfaces]⟩)) = _
          rw [CopyingRetainedContext.branch_left_input]
          exact congrArg Port.input (Fin.ext zero.symm)
        refine ⟨_,_,V,normal,normalizedFree,payload,0,?_⟩
        exact atInput ▸ mapped
      · cases n with
        | zero => exact False.elim (zero (by have := i.isLt; simp only [List.length_replicate] at *; omega))
        | succ n =>
          let j : Fin (List.replicate (n+1) Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩
          let retained := (CopyingRetainedContext.branch A (CopyRule.before (CopyRule.residualTree tree) A) true).comp (Occurrence.ofIso g)
          let payload := (inA.comp (Occurrence.serialRight (CopyRule.residual tree d) A)).comp retained
          obtain ⟨m,resolve⟩ := CopyRule.before_resolves_head (CopyRule.residualTree tree) A copyable j head
          have mapped := CopyTrace.resolves_map retained.matchEmbedding resolve
          have atInput : retained.ports (.input j) = .input i := by
            change Port.map _ ((CopyingRetainedContext.branch A (CopyRule.before (CopyRule.residualTree tree) A) true).ports (.input j)) = _
            rw [CopyingRetainedContext.branch_right_input]
            apply congrArg Port.input
            apply Fin.ext
            have := i.isLt
            simp only [j,List.length_replicate] at *
            omega
          refine ⟨_,_,V,normal,normalizedFree,payload,m+1,?_⟩
          exact atInput ▸ mapped

end Hypernets.Copying.CopyingTemplate
