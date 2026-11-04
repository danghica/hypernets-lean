import Hypernets.Copying.PropositionEnvironmentOpening

/-! Semantic regression checks for the actual allocated/opened intermediate:
retained store contents, atom resolution, size, and mixed environments. -/
namespace Hypernets.Copying.Proposition12_2
open Graph

def openedInstance : opened.Edge :=
  Serial.leftEdge _ _ (Application.argumentEdge body (primitiveNet 3 .instanceEdge) (0 : Fin 1))
def openedContraction : opened.Edge := ⟨true,⟨false,⟨false,(1 : Fin 2)⟩⟩⟩
def openedStore : opened.Edge := ⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩
def openedOne : opened.Edge := ⟨true,⟨true,(0 : Fin 1)⟩⟩

theorem opened_instance_label : opened.edgeLabel openedInstance = primitiveLabel 3 .instanceEdge := rfl
theorem opened_contraction_label : opened.edgeLabel openedContraction = primitiveLabel 3 (.contraction .atom) := rfl
theorem opened_store_label : opened.edgeLabel openedStore = primitiveLabel 3 .store := rfl
theorem opened_one_label : opened.edgeLabel openedOne = primitiveLabel 3 (.operation (.const (.nat 1))) := rfl

/-- The instance retained by beta still reaches the canonical atom contraction. -/
theorem opened_instance_hop : StoreTrace.Hop opened openedInstance openedContraction := by
  refine ⟨.inl opened_instance_label,?_⟩
  refine ⟨.internal (.inl (0 : Fin 1)),?_,?_⟩
  · change _ ∈ [_]; exact List.mem_cons_self
  · change _ ∈ [_,_]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The atom contraction is attached to the same shallow store. -/
theorem opened_contraction_hop : StoreTrace.Hop opened openedContraction openedStore := by
  refine ⟨.inr (.inl opened_contraction_label),?_⟩
  refine ⟨.internal (.inr ⟨true,.inr ⟨false,.inl (0 : Fin 1)⟩⟩),?_,?_⟩
  all_goals change _ ∈ [_]; exact List.mem_cons_self

theorem opened_resolves : StoreTrace.Resolves opened openedInstance openedStore 2 :=
  ⟨.step opened_instance_hop (.step opened_contraction_hop (.refl _)),opened_store_label⟩

theorem opened_resolves_unique {e n} (path : StoreTrace.Resolves opened openedInstance e n) :
    e = openedStore ∧ n = 2 := StoreTrace.resolves_unique path opened_resolves

/-- The retained store still contains the actual original numeral one. -/
theorem opened_store_content : opened.Adjacent openedStore openedOne := by
  refine ⟨.internal (.inr ⟨true,.inl (0 : Fin 1)⟩),?_,?_⟩
  all_goals change _ ∈ [_]; exact List.mem_cons_self

/-- The heap as a whole is not used as beta's stable argument. -/
theorem allocated_argument_not_stable : ¬ Stable (Allocation.after (numeral 3)) :=
  Allocation.after_not_stable _

theorem intermediate_edge_counts :
    (Translation.privateCell 0 0).finiteEdge.elements.length = 5 ∧
    allocated.finiteEdge.elements.length = 8 ∧
    betaSource.finiteEdge.elements.length = 8 ∧
    opened.finiteEdge.elements.length = 9 := by decide

theorem mixed_environment_opening :
    Combined.execution.Equiv CostOrder.any (originalInEnvironment 2 3) (openedInEnvironment 2 3) :=
  original_opened_environment 2 3
end Hypernets.Copying.Proposition12_2
