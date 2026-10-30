import Hypernets.Copying.ParametricityFamilyBlocks
import Hypernets.Copying.OccurrenceTensorBoundary

/-! Exact isolation of the first large or first small original abstraction.
The residual family keeps every other original abstraction in large-then-small
order. Its actual boundary action records the selected-input cyclic move. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyComponents
open Graph Opening
variable {d k : Nat} (A B : Hypernet d [.term] (List.replicate k .term))

/-- The literal tail of a nonempty ordered copy block. -/
noncomputable def tail (m : Nat) : Occurrence (copies A m) (copies A (m+1)) :=
  (BoxPullWeakening.ReverseComponents.tensorRight A (copies A m)).reboundaryTarget
    (by simp [List.replicate_succ])
    (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm])

theorem tail_input (m : Nat) (i : Fin (List.replicate m Wire.term).length) :
    (tail A m).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))

theorem tail_output (m : Nat) (i : Fin (List.replicate (k*m) Wire.term).length) :
    (tail A m).ports (.output i) = .output ⟨k+i.val,by
      have := i.isLt; simp only [List.length_replicate,Nat.mul_succ] at *; omega⟩ := by
  exact congrArg Port.output (Fin.ext (by change (List.replicate k Wire.term).length+i.val=k+i.val; simp))

noncomputable def largeTail (m n : Nat) : Occurrence (copies A m) (family A B (m+1) n) :=
  (tail A m).comp (largeBlock A B (m+1) n)
noncomputable def smallTail (m n : Nat) : Occurrence (copies B n) (family A B m (n+1)) :=
  (tail B n).comp (smallBlock A B m (n+1))

theorem largeTail_disjoint (m n : Nat) : ∀ e f,
    (largeTail A B m n).edges e ≠ (smallBlock A B (m+1) n).edges f := by
  intro e f eq
  have impossible : false = true := congrArg Sigma.fst eq
  cases impossible

theorem smallTail_disjoint (m n : Nat) : ∀ e f,
    (largeBlock A B m (n+1)).edges e ≠ (smallTail A B m n).edges f := by
  intro e f eq
  have impossible : false = true := congrArg Sigma.fst eq
  cases impossible

/-- Delete the first large member only; the residual blocks keep their
original large-then-small ordering and every complete recursive label. -/
noncomputable def remainingLarge (m n : Nat) : Occurrence (family A B m n) (family A B (m+1) n) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (largeTail A B m n)
    (smallBlock A B (m+1) n) (largeTail_disjoint A B m n)).reboundarySource _ _

/-- Delete the first small member only, retaining the complete original
large block before the remaining original small block. -/
noncomputable def remainingSmall (m n : Nat) : Occurrence (family A B m n) (family A B m (n+1)) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (largeBlock A B m (n+1))
    (smallTail A B m n) (smallTail_disjoint A B m n)).reboundarySource _ _

theorem remainingLarge_inputs (m n : Nat) : ∀ i, ((remainingLarge A B m n).ports (.input i)).IsInput := by
  intro i
  change ((BoxPullWeakening.ReverseComponents.tensorJoin (largeTail A B m n) (smallBlock A B (m+1) n) (largeTail_disjoint A B m n)).ports (.input ⟨i.val,by have := i.isLt; simpa only [List.length_replicate,List.length_append] using this⟩)).IsInput
  apply Occurrence.tensorJoin_inputs
  · intro j
    change ((largeBlock A B (m+1) n).ports ((tail A m).ports (.input j))).IsInput
    rw [tail_input,largeBlock_input]
    trivial
  · intro j
    rw [smallBlock_input]
    trivial

theorem remainingSmall_inputs (m n : Nat) : ∀ i, ((remainingSmall A B m n).ports (.input i)).IsInput := by
  intro i
  change ((BoxPullWeakening.ReverseComponents.tensorJoin (largeBlock A B m (n+1)) (smallTail A B m n) (smallTail_disjoint A B m n)).ports (.input ⟨i.val,by have := i.isLt; simpa only [List.length_replicate,List.length_append] using this⟩)).IsInput
  apply Occurrence.tensorJoin_inputs
  · intro j
    rw [largeBlock_input]
    trivial
  · intro j
    change ((smallBlock A B m (n+1)).ports ((tail B n).ports (.input j))).IsInput
    rw [tail_input,smallBlock_input]
    trivial

theorem remainingLarge_outputs (m n : Nat) : ∀ i, ((remainingLarge A B m n).ports (.output i)).IsOutput := by
  intro i
  change ((BoxPullWeakening.ReverseComponents.tensorJoin (largeTail A B m n) (smallBlock A B (m+1) n) (largeTail_disjoint A B m n)).ports (.output ⟨i.val,by have := i.isLt; simpa only [List.length_replicate,List.length_append,Nat.mul_add] using this⟩)).IsOutput
  apply Occurrence.tensorJoin_outputs
  · intro j
    change ((largeBlock A B (m+1) n).ports ((tail A m).ports (.output j))).IsOutput
    rw [tail_output,largeBlock_output]
    trivial
  · intro j
    rw [smallBlock_output]
    trivial

theorem remainingSmall_outputs (m n : Nat) : ∀ i, ((remainingSmall A B m n).ports (.output i)).IsOutput := by
  intro i
  change ((BoxPullWeakening.ReverseComponents.tensorJoin (largeBlock A B m (n+1)) (smallTail A B m n) (smallTail_disjoint A B m n)).ports (.output ⟨i.val,by have := i.isLt; simpa only [List.length_replicate,List.length_append,Nat.mul_add] using this⟩)).IsOutput
  apply Occurrence.tensorJoin_outputs
  · intro j
    rw [largeBlock_output]
    trivial
  · intro j
    change ((smallBlock A B m (n+1)).ports ((tail B n).ports (.output j))).IsOutput
    rw [tail_output,smallBlock_output]
    trivial

theorem firstLarge_disjoint (m n : Nat) : ∀ e f,
    (large A B (m+1) n ⟨0,by omega⟩).edges e ≠ (remainingLarge A B m n).edges f := by
  rintro e ⟨side,f⟩ eq
  cases side <;> cases eq

theorem firstSmall_disjoint (m n : Nat) : ∀ e f,
    (small A B m (n+1) ⟨0,by omega⟩).edges e ≠ (remainingSmall A B m n).edges f := by
  rintro e ⟨side,f⟩ eq
  cases side <;> cases eq

/-- The selected large abstraction followed by the remaining ordered family
is an actual complete occurrence covering the whole original family. -/
noncomputable def isolateLarge (m n : Nat) :
    Occurrence (Net.Tensor.net A (family A B m n)) (family A B (m+1) n) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (large A B (m+1) n ⟨0,by omega⟩)
    (remainingLarge A B m n) (firstLarge_disjoint A B m n)

/-- The selected small abstraction moves to the front explicitly. The
boundary isomorphism below records that move rather than pretending it fixes
all original external coordinates. -/
noncomputable def isolateSmall (m n : Nat) :
    Occurrence (Net.Tensor.net B (family A B m n)) (family A B m (n+1)) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (small A B m (n+1) ⟨0,by omega⟩)
    (remainingSmall A B m n) (firstSmall_disjoint A B m n)

theorem isolateLarge_cover (m n : Nat) : Function.Surjective (isolateLarge A B m n).edges := by
  rintro ⟨side,e⟩
  cases side
  · obtain ⟨part,e⟩ := e
    cases part
    · exact ⟨⟨false,e⟩,rfl⟩
    · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
  · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

theorem isolateSmall_cover (m n : Nat) : Function.Surjective (isolateSmall A B m n).edges := by
  rintro ⟨side,e⟩
  cases side
  · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
  · obtain ⟨part,e⟩ := e
    cases part
    · exact ⟨⟨false,e⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- The literal first-large isolation is a full recursive boundary
isomorphism, valid for arbitrary family sizes including empty remainders. -/
noncomputable def isolateLargeIso (m n : Nat) :
    BoundaryIso (Net.Tensor.net A (family A B m n)) (family A B (m+1) n) :=
  (isolateLarge A B m n).boundaryIso_of_edge_surjective
    (Occurrence.tensorJoin_inputs _ _ _ (by
      intro i; change Fin 1 at i; have zero : i = 0 := Subsingleton.elim _ _; subst i
      rw [large_input]; trivial) (remainingLarge_inputs A B m n))
    (Occurrence.tensorJoin_outputs _ _ _ (by intro i; rw [large_output]; trivial)
      (remainingLarge_outputs A B m n)) (isolateLarge_cover A B m n)

/-- First-small isolation records the simultaneous ordered input/private
output rotation. It also applies to the actual zero-output right family. -/
noncomputable def isolateSmallIso (m n : Nat) :
    BoundaryIso (Net.Tensor.net B (family A B m n)) (family A B m (n+1)) :=
  (isolateSmall A B m n).boundaryIso_of_edge_surjective
    (Occurrence.tensorJoin_inputs _ _ _ (by
      intro i; change Fin 1 at i; have zero : i = 0 := Subsingleton.elim _ _; subst i
      rw [small_input]; trivial) (remainingSmall_inputs A B m n))
    (Occurrence.tensorJoin_outputs _ _ _ (by intro i; rw [small_output]; trivial)
      (remainingSmall_outputs A B m n)) (isolateSmall_cover A B m n)

end Hypernets.Copying.Parametricity.FamilyComponents
