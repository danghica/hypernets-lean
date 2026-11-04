import Hypernets.Copying.AtomicEmbeddingIdentity

/-! Exhaustive old-graph plus weakening partitions for all original atomic
clauses, with the new wire inserted between the term and atom blocks. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Atomic
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (termResource atomResource termResource_injective atomResource_injective)

theorem termResource_term (k : Nat) : (termResource .term : Fin k → Fin (k+1)) = Fin.castSucc := rfl
theorem termResource_atom (k : Nat) : (termResource .atom : Fin k → Fin k) = id := rfl
theorem atomResource_term (h : Nat) : (atomResource .term : Fin h → Fin h) = id := rfl
theorem atomResource_atom (h : Nat) : (atomResource .atom : Fin h → Fin (h+1)) = Fin.succ := rfl

noncomputable def variableComplement (d : Nat) {k} (h : Nat) (i : Fin k) (s : ShareSort) :
    Complement s (Translation.variableTerm d h i)
      (Translation.variableTerm d (atoms s h) (termResource s i)) := by
  cases s
  · exact ((selectedComplement .term d (ResourceGap.append k) i).tensorRight
      (Distributor.atDepth .atom h 0 d)).castInterfaces (by simp [ShareSort.wire]) rfl
        (by simp [ShareSort.wire]) rfl
  · exact ((forestComplement .atom d (ResourceGap.prepend h)).tensorLeft
      (Translation.selectedResource d .term i)).castInterfaces (by simp [ShareSort.wire]) rfl
        (by simp [ShareSort.wire]) rfl

noncomputable def atomComplement (d k : Nat) {h} (a : Fin h) (s : ShareSort) :
    Complement s (Translation.atom d k a)
      (Translation.atom d (variables s k) (atomResource s a)) := by
  cases s
  · exact ((forestComplement .term d (ResourceGap.append k)).tensorRight
      (Serial.net (primitiveNet d .instanceEdge) (Translation.selectedResource d .atom a))).castInterfaces
        (by simp [primitiveSignature]) rfl (by simp [primitiveSignature]) rfl
  · let q := selectedComplement .atom d (ResourceGap.prepend h) a
    have inputs : ∀ i, q.old.ports (.input i) = .input i := by
      intro i; rw [selectedComplement_old]; exact SelectedResource.embedding_input _ _ _ _ _ i
    exact ((q.serialPrefix (primitiveNet d .instanceEdge) inputs).tensorLeft
      (Distributor.atDepth .term k 0 d)).castInterfaces
        (by simp [primitiveSignature]) rfl (by simp [primitiveSignature]) rfl

noncomputable def constantComplement (d k h : Nat) (c : Constant) (s : ShareSort) :
    Complement s (Translation.constant d k h c)
      (Translation.constant d (variables s k) (atoms s h) c) := by
  cases s
  · exact (((forestComplement .term d (ResourceGap.append k)).tensorRight
      (primitiveNet d (.operation (.const c)))).tensorRight (Distributor.atDepth .atom h 0 d)).castInterfaces
        (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,atoms])
        (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,atoms])
  · exact ((forestComplement .atom d (ResourceGap.prepend h)).tensorLeft
      (Net.Tensor.net (Distributor.atDepth .term k 0 d) (primitiveNet d (.operation (.const c))))).castInterfaces
        (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,atoms])
        (by simp [primitiveSignature]) (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire,variables,atoms])

theorem variableComplement_old (d : Nat) {k} (h : Nat) (i : Fin k) (s : ShareSort) :
    (variableComplement d h i s).old = variableMap (termResource s) (atomResource s)
      (termResource_injective s) (atomResource_injective s) i := by
  cases s <;> simp only [variableComplement,Complement.castInterfaces_old,Complement.tensorRight,
    Complement.tensorLeft,selectedComplement_old,forestComplement,variableMap,termResource_term,termResource_atom,atomResource_term,atomResource_atom,ResourceGap.append,ResourceGap.prepend,
    forestEmbedding_id,selectedEmbedding_id]
  all_goals rfl

theorem atomComplement_old (d k : Nat) {h} (a : Fin h) (s : ShareSort) :
    (atomComplement d k a s).old = atom (termResource s) (atomResource s)
      (termResource_injective s) (atomResource_injective s) a := by
  cases s <;> simp only [atomComplement,Complement.castInterfaces_old,Complement.tensorRight,
    Complement.tensorLeft,Complement.serialPrefix,selectedComplement_old,forestComplement,atom,termResource_term,termResource_atom,atomResource_term,atomResource_atom,ResourceGap.append,ResourceGap.prepend,
    forestEmbedding_id,selectedEmbedding_id,serialPrefix_identity]
  all_goals rfl

theorem constantComplement_old (d k h : Nat) (c : Constant) (s : ShareSort) :
    (constantComplement d k h c s).old = constant (termResource s) (atomResource s)
      (termResource_injective s) (atomResource_injective s) c := by
  cases s <;> simp only [constantComplement,Complement.castInterfaces_old,Complement.tensorRight,
    Complement.tensorLeft,forestComplement,constant,termResource_term,termResource_atom,atomResource_term,atomResource_atom,ResourceGap.append,ResourceGap.prepend,forestEmbedding_id,tensorMap_identity]
  all_goals rfl
end Hypernets.Copying.Weakening.Atomic
