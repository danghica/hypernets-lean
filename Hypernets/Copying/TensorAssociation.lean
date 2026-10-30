import Hypernets.Copying.OccurrenceTensorBoundary
import Hypernets.Copying.OccurrenceBoundaryCoverIso

/-! Association of the literal disjoint tensor assembly. It changes only
parenthesization, preserving the complete ordered external boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TensorAssociation
open Graph Opening
variable {d I O J K U V} (A : Hypernet d I O) (B : Hypernet d J K) (C : Hypernet d U V)

noncomputable def first : Occurrence A (Net.Tensor.net A (Net.Tensor.net B C)) :=
  BoxPullWeakening.ReverseComponents.tensorLeft A (Net.Tensor.net B C)
noncomputable def second : Occurrence B (Net.Tensor.net A (Net.Tensor.net B C)) :=
  (BoxPullWeakening.ReverseComponents.tensorLeft B C).comp
    (BoxPullWeakening.ReverseComponents.tensorRight A (Net.Tensor.net B C))
noncomputable def third : Occurrence C (Net.Tensor.net A (Net.Tensor.net B C)) :=
  (BoxPullWeakening.ReverseComponents.tensorRight B C).comp
    (BoxPullWeakening.ReverseComponents.tensorRight A (Net.Tensor.net B C))

theorem first_second : ∀ e f, (first A B C).edges e ≠ (second A B C).edges f := by
  intro e f eq; cases eq
noncomputable def firstTwo : Occurrence (Net.Tensor.net A B) (Net.Tensor.net A (Net.Tensor.net B C)) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (first A B C) (second A B C) (first_second A B C)
theorem firstTwo_third : ∀ e f, (firstTwo A B C).edges e ≠ (third A B C).edges f := by
  rintro ⟨part,e⟩ f eq; cases part <;> cases eq
noncomputable def occurrence : Occurrence (Net.Tensor.net (Net.Tensor.net A B) C)
    (Net.Tensor.net A (Net.Tensor.net B C)) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (firstTwo A B C) (third A B C) (firstTwo_third A B C)

theorem inputs : ∀ i, ((occurrence A B C).ports (.input i)).IsInput := by
  apply Occurrence.tensorJoin_inputs
  · exact Occurrence.tensorJoin_inputs _ _ _ (fun _ => trivial) (fun _ => trivial)
  · intro i; trivial

theorem outputs : ∀ i, ((occurrence A B C).ports (.output i)).IsOutput := by
  apply Occurrence.tensorJoin_outputs
  · exact Occurrence.tensorJoin_outputs _ _ _ (fun _ => trivial) (fun _ => trivial)
  · intro i; trivial

theorem cover : Function.Surjective (occurrence A B C).edges := by
  rintro ⟨part,e⟩
  cases part
  · exact ⟨⟨false,⟨false,e⟩⟩,rfl⟩
  · obtain ⟨part,e⟩ := e
    cases part
    · exact ⟨⟨false,⟨true,e⟩⟩,rfl⟩
    · exact ⟨⟨true,e⟩,rfl⟩

/-- The isomorphism retains each original component and its ordered ports. -/
noncomputable def iso : BoundaryIso (Net.Tensor.net (Net.Tensor.net A B) C)
    (Net.Tensor.net A (Net.Tensor.net B C)) :=
  (occurrence A B C).boundaryIso_of_edge_surjective (inputs A B C) (outputs A B C) (cover A B C)

theorem input (i : Fin ((I++J)++U).length) :
    (iso A B C).ports.toFun (.input i) = .input ⟨i.val,by simpa [List.length_append,Nat.add_assoc] using i.isLt⟩ := by
  let p := Net.Tensor.split (I++J) U i
  have eq := Net.Tensor.join_split (I++J) U i
  change Net.Tensor.join (I++J) U p = i at eq
  obtain ⟨side,j⟩ := p
  cases side
  · have outer : (BoxPullWeakening.ReverseComponents.tensorLeft (Net.Tensor.net A B) C).ports (.input j) = .input i := congrArg Port.input eq
    change (occurrence A B C).ports (.input i) = _
    rw [← outer,occurrence,Occurrence.tensorJoin_left]
    let p := Net.Tensor.split I J j
    have eq' := Net.Tensor.join_split I J j
    change Net.Tensor.join I J p = j at eq'
    obtain ⟨part,l⟩ := p
    cases part
    · have inner : (BoxPullWeakening.ReverseComponents.tensorLeft A B).ports (.input l) = .input j := congrArg Port.input eq'
      rw [← inner,firstTwo,Occurrence.tensorJoin_left]
      exact congrArg Port.input (Fin.ext ((congrArg Fin.val eq').trans (congrArg Fin.val eq)))
    · have inner : (BoxPullWeakening.ReverseComponents.tensorRight A B).ports (.input l) = .input j := congrArg Port.input eq'
      rw [← inner,firstTwo,Occurrence.tensorJoin_right]
      exact congrArg Port.input (Fin.ext ((congrArg Fin.val eq').trans (congrArg Fin.val eq)))
  · have outer : (BoxPullWeakening.ReverseComponents.tensorRight (Net.Tensor.net A B) C).ports (.input j) = .input i := congrArg Port.input eq
    change (occurrence A B C).ports (.input i) = _
    rw [← outer,occurrence,Occurrence.tensorJoin_right]
    apply congrArg Port.input
    apply Fin.ext
    have h := congrArg Fin.val eq
    change (I++J).length+j.val=i.val at h
    change I.length+(J.length+j.val)=i.val
    simp only [List.length_append] at h
    omega

theorem output (i : Fin ((O++K)++V).length) :
    (iso A B C).ports.toFun (.output i) = .output ⟨i.val,by simpa [List.length_append,Nat.add_assoc] using i.isLt⟩ := by
  let p := Net.Tensor.split (O++K) V i
  have eq := Net.Tensor.join_split (O++K) V i
  change Net.Tensor.join (O++K) V p = i at eq
  obtain ⟨side,j⟩ := p
  cases side
  · have outer : (BoxPullWeakening.ReverseComponents.tensorLeft (Net.Tensor.net A B) C).ports (.output j) = .output i := congrArg Port.output eq
    change (occurrence A B C).ports (.output i) = _
    rw [← outer,occurrence,Occurrence.tensorJoin_left]
    let p := Net.Tensor.split O K j
    have eq' := Net.Tensor.join_split O K j
    change Net.Tensor.join O K p = j at eq'
    obtain ⟨part,l⟩ := p
    cases part
    · have inner : (BoxPullWeakening.ReverseComponents.tensorLeft A B).ports (.output l) = .output j := congrArg Port.output eq'
      rw [← inner,firstTwo,Occurrence.tensorJoin_left]
      exact congrArg Port.output (Fin.ext ((congrArg Fin.val eq').trans (congrArg Fin.val eq)))
    · have inner : (BoxPullWeakening.ReverseComponents.tensorRight A B).ports (.output l) = .output j := congrArg Port.output eq'
      rw [← inner,firstTwo,Occurrence.tensorJoin_right]
      exact congrArg Port.output (Fin.ext ((congrArg Fin.val eq').trans (congrArg Fin.val eq)))
  · have outer : (BoxPullWeakening.ReverseComponents.tensorRight (Net.Tensor.net A B) C).ports (.output j) = .output i := congrArg Port.output eq
    change (occurrence A B C).ports (.output i) = _
    rw [← outer,occurrence,Occurrence.tensorJoin_right]
    apply congrArg Port.output
    apply Fin.ext
    have h := congrArg Fin.val eq
    change (O++K).length+j.val=i.val at h
    change O.length+(K.length+j.val)=i.val
    simp only [List.length_append] at h
    omega

end Hypernets.Copying.TensorAssociation
