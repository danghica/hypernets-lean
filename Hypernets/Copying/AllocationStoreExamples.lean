import Hypernets.Copying.AllocationExecution

/-! Store identity and exact resolution for executions of the unchanged ref translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.StoreTrace
open Graph

/-- Attaching a continuation preserves atom hops wholly within the left graph. -/
theorem hop_serial_left {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) {a b : G.Edge}
    (h : Hop G a b) : Hop (Serial.net G H) (Serial.leftEdge G H a) (Serial.leftEdge G H b) := by
  constructor
  · change ForwardLabel d ((Serial.net G H).edgeLabel (Serial.leftEdge G H a))
    rw [Serial.leftEdge_label]; exact h.1
  · obtain ⟨v,ha,hb⟩ := h.2
    refine ⟨BoundarySerial.leftInsert G H v,?_,?_⟩
    · cases d <;> exact List.mem_map_of_mem ha
    · cases d <;> exact List.mem_map_of_mem hb

theorem resolves_serial_left {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)
    {a b : G.Edge} {n} (h : Resolves G a b n) :
    Resolves (Serial.net G H) (Serial.leftEdge G H a) (Serial.leftEdge G H b) n :=
  ⟨h.1.map (Serial.leftEdge G H) (hop_serial_left G H), (Serial.leftEdge_label G H b).trans h.2⟩
end Hypernets.Copying.StoreTrace
namespace Hypernets.Copying.Allocation
open Graph

/-- The returned reference occurrence in the exact translated execution's result. -/
def allocatedInstance (n : Nat) : (allocatedGraph n).Edge :=
  Serial.leftEdge _ _ (instanceEdge (constantArgument n))

def allocatedStore (n : Nat) : (allocatedGraph n).Edge :=
  Serial.leftEdge _ _ (store (constantArgument n))

/-- Resolution is proved in the graph actually reached by the five-step execution. -/
theorem allocated_resolves (n : Nat) :
    StoreTrace.Resolves (allocatedGraph n) (allocatedInstance n) (allocatedStore n) 2 :=
  StoreTrace.resolves_serial_left _ _ (resolves (constantArgument n))

theorem allocated_resolves_exact (n : Nat) {e m}
    (h : StoreTrace.Resolves (allocatedGraph n) (allocatedInstance n) e m) :
    e = allocatedStore n ∧ m = 2 := StoreTrace.resolves_unique h (allocated_resolves n)

/-- The stored constant edge is an old edge, distinct from the allocated store. -/
def allocatedValue (n : Nat) : (allocatedGraph n).Edge :=
  Serial.leftEdge _ _ (oldEdge (constantArgument n) ⟨false,⟨true,(0 : Fin 1)⟩⟩)

theorem allocated_value_label (n : Nat) :
    (allocatedGraph n).edgeLabel (allocatedValue n) = primitiveLabel 0 (.operation (.const (.nat n))) := rfl

/-- The resolved store points to that literal value, with no rewriting of its contents. -/
theorem allocated_store_value (n : Nat) :
    (allocatedGraph n).target (allocatedStore n) = (allocatedGraph n).source (allocatedValue n) := rfl

/-- The one used in Proposition 12.2 really is a reference containing the literal one. -/
theorem ref_one :
    (machine 0 []).Steps 5 ⟨Translation.term (Term.unary (k := 0) (h := 0) .ref (.const (.nat 1))),(.search,.input 0)⟩
      ⟨allocatedGraph 1,(.backtrack,.input 0)⟩ ∧
    StoreTrace.Resolves (allocatedGraph 1) (allocatedInstance 1) (allocatedStore 1) 2 ∧
    (allocatedGraph 1).target (allocatedStore 1) = (allocatedGraph 1).source (allocatedValue 1) :=
  ⟨reference_run 1,allocated_resolves 1,allocated_store_value 1⟩

/-- The concrete successful execution cannot continue after returning its reference. -/
theorem reference_final_normal (n : Nat) (t : State 0 []) :
    ¬ Step ⟨allocatedGraph n,(.backtrack,.input 0)⟩ t := completed_normal (reference_completes n) t
end Hypernets.Copying.Allocation
