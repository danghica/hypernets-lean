import Hypernets.Copying.ParametricityFamilyComponents
import Hypernets.Copying.OccurrenceBoundaryCoverIso

/-! The two ordered Figure20 families are separated as their actual complete
large and small blocks, with exact input and private-output offsets. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyComponents
open Graph Opening
variable {d k : Nat} (A B : Hypernet d [.term] (List.replicate k .term))

/-- The original tensor of large and small copies, exposing its arithmetic
interface equality uniformly for the one-output and zero-output families. -/
def family (m n : Nat) : Hypernet d (List.replicate (m+n) .term) (List.replicate (k*(m+n)) .term) :=
  (Net.Tensor.net (copies A m) (copies B n)).reboundary
    (by rw [List.replicate_append_replicate])
    (by rw [List.replicate_append_replicate,Nat.mul_add])

noncomputable def largeBlock (m n : Nat) : Occurrence (copies A m) (family A B m n) :=
  (BoxPullWeakening.ReverseComponents.tensorLeft (copies A m) (copies B n)).reboundaryTarget _ _
noncomputable def smallBlock (m n : Nat) : Occurrence (copies B n) (family A B m n) :=
  (BoxPullWeakening.ReverseComponents.tensorRight (copies A m) (copies B n)).reboundaryTarget _ _

/-- Whole blocks retain their literal ordered coordinates. -/
theorem largeBlock_input (m n : Nat) (i : Fin (List.replicate m Wire.term).length) :
    (largeBlock A B m n).ports (.input i) = .input ⟨i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := rfl

theorem smallBlock_input (m n : Nat) (i : Fin (List.replicate n Wire.term).length) :
    (smallBlock A B m n).ports (.input i) = .input ⟨m+i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  exact congrArg Port.input (Fin.ext (by change (List.replicate m Wire.term).length+i.val=m+i.val; simp))

theorem largeBlock_output (m n : Nat) (i : Fin (List.replicate (k*m) Wire.term).length) :
    (largeBlock A B m n).ports (.output i) = .output ⟨i.val,by
      have := i.isLt; simp only [List.length_replicate,Nat.mul_add] at *; omega⟩ := rfl

theorem smallBlock_output (m n : Nat) (i : Fin (List.replicate (k*n) Wire.term).length) :
    (smallBlock A B m n).ports (.output i) = .output ⟨k*m+i.val,by
      have := i.isLt; simp only [List.length_replicate,Nat.mul_add] at *; omega⟩ := by
  exact congrArg Port.output (Fin.ext (by change (List.replicate (k*m) Wire.term).length+i.val=k*m+i.val; simp))

noncomputable def large (m n : Nat) (i : Fin m) : Occurrence A (family A B m n) :=
  (copy A m i).comp (largeBlock A B m n)
noncomputable def small (m n : Nat) (i : Fin n) : Occurrence B (family A B m n) :=
  (copy B n i).comp (smallBlock A B m n)

theorem large_input (m n : Nat) (i : Fin m) :
    (large A B m n i).ports (.input 0) = .input ⟨i.val,by simp; omega⟩ := by
  change (largeBlock A B m n).ports ((copy A m i).ports (.input 0)) = _
  rw [copy_input,largeBlock_input]

theorem small_input (m n : Nat) (i : Fin n) :
    (small A B m n i).ports (.input 0) = .input ⟨m+i.val,by simp⟩ := by
  change (smallBlock A B m n).ports ((copy B n i).ports (.input 0)) = _
  rw [copy_input,smallBlock_input]

/-- The private-output row follows exactly the same large-block ordering. -/
theorem large_output (m n : Nat) (i : Fin m) (j : Fin (List.replicate k Wire.term).length) :
    (large A B m n i).ports (.output j) = .output ⟨k*i.val+j.val,by
      have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      have h := j.isLt
      simp only [Nat.mul_succ,List.length_replicate,Nat.mul_add] at *
      omega⟩ := by
  change (largeBlock A B m n).ports ((copy A m i).ports (.output j)) = _
  rw [copy_output,largeBlock_output]

/-- Small private outputs follow all large outputs and retain their own
within-copy ordering. Empty-output families satisfy the same statement. -/
theorem small_output (m n : Nat) (i : Fin n) (j : Fin (List.replicate k Wire.term).length) :
    (small A B m n i).ports (.output j) = .output ⟨k*m+(k*i.val+j.val),by
      have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      have h := j.isLt
      simp only [Nat.mul_succ,List.length_replicate,Nat.mul_add] at *
      omega⟩ := by
  change (smallBlock A B m n).ports ((copy B n i).ports (.output j)) = _
  rw [copy_output,smallBlock_output]

/-- Large/small component ownership never aliases, independently of their
bodies or of any isomorphism between two lambda representations. -/
theorem blocks_disjoint (m n : Nat) : ∀ e f,
    (largeBlock A B m n).edges e ≠ (smallBlock A B m n).edges f := by
  intro e f eq
  have impossible : false = true := congrArg Sigma.fst eq
  cases impossible

/-- Every family edge belongs to one actual original indexed abstraction. -/
theorem family_cover (m n : Nat) (e : (family A B m n).Edge) :
    (∃ i : Fin m, ∃ a, (large A B m n i).edges a = e) ∨
    (∃ i : Fin n, ∃ b, (small A B m n i).edges b = e) := by
  obtain ⟨side,e⟩ := e
  cases side
  · obtain ⟨i,a,eq⟩ := copy_cover A m e
    exact .inl ⟨i,a,congrArg (fun x => (largeBlock A B m n).edges x) eq⟩
  · obtain ⟨i,a,eq⟩ := copy_cover B n e
    exact .inr ⟨i,a,congrArg (fun x => (smallBlock A B m n).edges x) eq⟩

end Hypernets.Copying.Parametricity.FamilyComponents
