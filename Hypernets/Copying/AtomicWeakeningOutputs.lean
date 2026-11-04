import Hypernets.Copying.AtomicWeakeningComplements

/-! The added edge in each original atomic clause occupies the new resource
position, while all old resources follow the same insertion map. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Atomic
open Graph Opening BoxPullWeakening EnvironmentPermutation
open BoxPullWeakening.RetainedCopy (termResource atomResource outputIndex)

theorem variableComplement_output (d : Nat) {k} (h : Nat) (i : Fin k) (s : ShareSort) (v : Fin 1) :
    (variableComplement d h i s).added.ports (.output v) = .output (CopyRow.addedOutput k h s) := by
  cases s
  · let q := selectedComplement .term d (ResourceGap.append k) i
    let X := Distributor.atDepth .atom h 0 d
    have law := q.tensorRight_added_output X v _ (selectedComplement_output _ _ _ i v)
    exact (q.tensorRight X).castInterfaces_added_output
      (by simp [ShareSort.wire]) rfl (by simp [ShareSort.wire]) rfl v _ law
  · let q := forestComplement .atom d (ResourceGap.prepend h)
    let X := Translation.selectedResource d .term i
    have law := q.tensorLeft_added_output X v _ (forestComplement_output _ _ _ v)
    have mapped := (q.tensorLeft X).castInterfaces_added_output
      (U := [.term]) (V := environmentInterface k h) (W := [.term]) (X := environmentInterface k (h+1))
      (by simp [ShareSort.wire]) rfl (by simp [ShareSort.wire]) rfl v _ law
    simp only [Net.Tensor.join,List.length_replicate,Fin.cast,Nat.add_zero] at mapped
    exact mapped

theorem atomComplement_output (d k : Nat) {h} (a : Fin h) (s : ShareSort) (v : Fin 1) :
    (atomComplement d k a s).added.ports (.output v) = .output (CopyRow.addedOutput k h s) := by
  cases s
  · let q := forestComplement .term d (ResourceGap.append k)
    let X := Serial.net (primitiveNet d .instanceEdge) (Translation.selectedResource d .atom a)
    have law := q.tensorRight_added_output X v _ (forestComplement_output _ _ _ v)
    exact (q.tensorRight X).castInterfaces_added_output
      (by simp [primitiveSignature]) rfl (by simp [primitiveSignature]) rfl v _ law
  · let q := selectedComplement .atom d (ResourceGap.prepend h) a
    have inputs : ∀ i, q.old.ports (.input i) = .input i := by
      intro i; rw [selectedComplement_old]; exact SelectedResource.embedding_input _ _ _ _ _ i
    let P := primitiveNet d .instanceEdge
    let X := Distributor.atDepth .term k 0 d
    have law := (q.serialPrefix P inputs).tensorLeft_added_output X v _
      (q.serialPrefix_added_output P inputs v _ (selectedComplement_output _ _ _ a v))
    have mapped := ((q.serialPrefix P inputs).tensorLeft X).castInterfaces_added_output
      (U := [.term]) (V := environmentInterface k h) (W := [.term]) (X := environmentInterface k (h+1))
      (by simp [primitiveSignature]) rfl (by simp [primitiveSignature]) rfl v _ law
    simp only [Net.Tensor.join,List.length_replicate,Fin.cast,Nat.add_zero] at mapped
    exact mapped

theorem constantComplement_output (d k h : Nat) (c : Constant) (s : ShareSort) (v : Fin 1) :
    (constantComplement d k h c s).added.ports (.output v) = .output (CopyRow.addedOutput k h s) := by
  cases s
  · let q := forestComplement .term d (ResourceGap.append k)
    let P := primitiveNet d (.operation (.const c))
    let X := Distributor.atDepth .atom h 0 d
    have law := (q.tensorRight P).tensorRight_added_output X v _
      (q.tensorRight_added_output P v _ (forestComplement_output _ _ _ v))
    exact ((q.tensorRight P).tensorRight X).castInterfaces_added_output
      (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,BoxPullWeakening.atoms])
      (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,BoxPullWeakening.atoms]) v _ law
  · let q := forestComplement .atom d (ResourceGap.prepend h)
    let X := Net.Tensor.net (Distributor.atDepth .term k 0 d) (primitiveNet d (.operation (.const c)))
    have law := q.tensorLeft_added_output X v _ (forestComplement_output _ _ _ v)
    have mapped := (q.tensorLeft X).castInterfaces_added_output
      (U := [.term]) (V := environmentInterface k h) (W := [.term]) (X := environmentInterface k (h+1))
      (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,BoxPullWeakening.atoms])
      (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,BoxPullWeakening.atoms]) v _ law
    simp only [Net.Tensor.join,List.length_replicate,List.length_append,primitiveSignature,
      Operation.outputs,List.length_nil,Nat.add_zero,Fin.cast] at mapped
    exact mapped

/-- The two ordered environment blocks exhaust every external output. -/
theorem environment_output {d I k h s} {G : Hypernet d I (environmentInterface k h)}
    {H : Hypernet d I (environmentInterface (variables s k) (atoms s h))} (f : Occurrence G H)
    (terms : ∀ i, f.ports (.output (termIndex i)) = .output (termIndex (termResource s i)))
    (atoms : ∀ a, f.ports (.output (atomIndex a)) = .output (atomIndex (atomResource s a)))
    (i : Fin (environmentInterface k h).length) : f.ports (.output i) = .output (outputIndex s i) := by
  by_cases term : i.val < k
  · let x : Fin k := ⟨i.val,term⟩
    have eq : termIndex (h := h) x = i := Fin.ext rfl
    rw [← eq,terms,RetainedCopy.outputIndex_term]
  · let a : Fin h := ⟨i.val-k,by have bound := i.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at bound; omega⟩
    have eq : atomIndex (k := k) a = i := Fin.ext (by change k+(i.val-k)=i.val; omega)
    rw [← eq,atoms,RetainedCopy.outputIndex_atom]
end Hypernets.Copying.Weakening.Atomic
