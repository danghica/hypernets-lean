import Hypernets.Copying.AssignmentSafety

/-! Actual translated literal payloads and preserved old contents after update. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

def literalEdge (n : Nat) : (Allocation.constantArgument n).Edge := ⟨false,⟨true,(0 : Fin 1)⟩⟩

theorem translated_value_returns {h} (T : ContractionTree .atom (h+1)) (n : Nat) :
    Search.Step (before T (Allocation.constantArgument n))
      (.search,valueArgument T _) (.backtrack,valueArgument T _) := by
  apply Search.Step.search (beforeValue T _ (literalEdge n)) (.operation (.const (.nat n))) _ _ rfl
  change _ ∈ [_]; exact List.mem_cons_self
  rfl

/-- Seven local transitions with the original Figure 16 literal translation retained. -/
theorem translated_value_run {h} (T : ContractionTree .atom (h+1)) (n : Nat) :
    (machine 0 h []).Steps 7
      ⟨before T (Allocation.constantArgument n),(.search,inputPort h [] 0)⟩
      ⟨after T (Allocation.constantArgument n),(.backtrack,inputPort h [] 0)⟩ :=
  .cons (.search _ (search_instance T _)) (.cons (.search _ (instance_returns T _))
    (.cons (.search _ (search_value T _)) (.cons (.search _ (translated_value_returns T n))
      (.cons (.search _ (ready T _)) (.cons (.assign T _ (Allocation.constantArgument_stable n))
        (.cons (.search _ (unit_returns T _)) (.zero _)))))))

/-- A heap update keeps both actual translated literals: one stored, the other weakened. -/
def updatedHeap {h} (T : ContractionTree .atom (h+1)) (old new : Nat) :=
  withContents T (Allocation.constantArgument new) (Allocation.constantArgument old)
def updatedCell {h} (T : ContractionTree .atom (h+1)) (old new : Nat) : (updatedHeap T old new).Edge :=
  Serial.leftEdge _ _ (afterStore T (Allocation.constantArgument new))
def updatedValue {h} (T : ContractionTree .atom (h+1)) (old new : Nat) : (updatedHeap T old new).Edge :=
  Serial.leftEdge _ _ (afterValue T (Allocation.constantArgument new) (literalEdge new))
def discardedValue {h} (T : ContractionTree .atom (h+1)) (old new : Nat) : (updatedHeap T old new).Edge :=
  Serial.rightEdge _ _ (literalEdge old)
def oldWeakening {h} (T : ContractionTree .atom (h+1)) (old new : Nat) : (updatedHeap T old new).Edge :=
  Serial.leftEdge _ _ (discardOld T (Allocation.constantArgument new))

theorem updated_literal {h} (T : ContractionTree .atom (h+1)) (old new : Nat) :
    (updatedHeap T old new).edgeLabel (updatedValue T old new) = primitiveLabel 0 (.operation (.const (.nat new))) ∧
    (updatedHeap T old new).target (updatedCell T old new) = (updatedHeap T old new).source (updatedValue T old new) := ⟨rfl,rfl⟩

theorem discarded_literal {h} (T : ContractionTree .atom (h+1)) (old new : Nat) :
    (updatedHeap T old new).edgeLabel (discardedValue T old new) = primitiveLabel 0 (.operation (.const (.nat old))) ∧
    (updatedHeap T old new).edgeLabel (oldWeakening T old new) = primitiveLabel 0 (.weakening .term) ∧
    (updatedHeap T old new).target (oldWeakening T old new) = (updatedHeap T old new).source (discardedValue T old new) := ⟨rfl,rfl,rfl⟩

/-- Discarded contents have not been identified with the new stored contents. -/
theorem old_new_disjoint {h} (T : ContractionTree .atom (h+1)) (old new : Nat) :
    updatedValue T old new ≠ discardedValue T old new := by
  intro eq
  have bad := congrArg Sigma.fst eq
  cases bad

/-- Even with another reference and a noncanonical tree, literal one is replaced by two,
while the old literal one persists behind its weakening. -/
theorem one_to_two :
    (updatedHeap (Examples.binaryTree .atom) 1 2).target (updatedCell (Examples.binaryTree .atom) 1 2) =
      (updatedHeap (Examples.binaryTree .atom) 1 2).source (updatedValue (Examples.binaryTree .atom) 1 2) ∧
    (updatedHeap (Examples.binaryTree .atom) 1 2).target (oldWeakening (Examples.binaryTree .atom) 1 2) =
      (updatedHeap (Examples.binaryTree .atom) 1 2).source (discardedValue (Examples.binaryTree .atom) 1 2) :=
  ⟨(updated_literal _ 1 2).2,(discarded_literal _ 1 2).2.2⟩
end Hypernets.Copying.Assignment
