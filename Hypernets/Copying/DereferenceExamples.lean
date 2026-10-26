import Hypernets.Copying.DereferenceSafety
import Hypernets.Copying.TracingExamples

/-! Canonical and noncanonical read matches, literal stored one, and copy handoff. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

/-- The one-reference canonical atom tree used by allocation resolves in two hops. -/
theorem canonical_resolves_before (d : Nat) :
    StoreTrace.Resolves (before (ContractionTree.canonical .atom 1) d)
      (beforeInstance (ContractionTree.canonical .atom 1) d)
      (beforeStore (ContractionTree.canonical .atom 1) d) 2 := by
  let T := ContractionTree.canonical .atom 1
  have rootEq : T.root = (1 : Fin 2) := T.net.target_unique T.root_output (by change (Port.output (0 : Fin 1) : Port (Fin 1) 1 1) ∈ [.output 0]; simp)
  refine ⟨.step (enters_before T d (1 : Fin 2) (by change (Port.input (0 : Fin 1) : Port (Fin 1) 1 1) ∈ [.internal 0,.input 0]; simp)) (.step ?_ (.refl _)),rfl⟩
  simpa only [rootEq] using root_before T d

theorem canonical_resolves_after (d : Nat) :
    StoreTrace.Resolves (after (ContractionTree.canonical .atom 1) d)
      (afterInstance (ContractionTree.canonical .atom 1) d)
      (afterStore (ContractionTree.canonical .atom 1) d) 2 :=
  (resolution_count_iff _ d 2).mp (canonical_resolves_before d)

/-- A noncanonical tree without a weakening is also a valid two-reference match. -/
theorem binary_resolves_before (d : Nat) :
    StoreTrace.Resolves (before (Examples.binaryTree .atom) d)
      (beforeInstance (Examples.binaryTree .atom) d)
      (beforeStore (Examples.binaryTree .atom) d) 2 := by
  let T := Examples.binaryTree .atom
  have rootEq : T.root = (0 : Fin 1) := by
    apply Fin.ext; change T.root.val = 0
    have bound := T.root.isLt; change T.root.val < 1 at bound; omega
  refine ⟨.step (enters_before T d (0 : Fin 1) (by change (Port.input (0 : Fin 2) : Port Empty 2 1) ∈ [.input 0,.input 1]; simp)) (.step ?_ (.refl _)),rfl⟩
  simpa only [rootEq] using root_before T d

/-- The second reference remains at the same external atom input after this read. -/
theorem binary_other_reference (d : Nat) :
    afterTreeVertex (Examples.binaryTree .atom) d (.input (1 : Fin 2)) = inputPort 1 (1 : Fin 2) :=
  after_other_input _ d (0 : Fin 1)

/-- The general execution handles the noncanonical match without a new machine axiom. -/
theorem binary_read_run (d : Nat) :
    (machine d 1).Steps 5 ⟨before (Examples.binaryTree .atom) d,(.search,inputPort 1 0)⟩
      ⟨after (Examples.binaryTree .atom) d,(.rewrite,inputPort 1 0)⟩ := read_run _ d

/-- The copied output is still connected to the original translation of literal one. -/
def storedOne := withContent (ContractionTree.canonical .atom 1) (Allocation.constantArgument 1)

def storedOneValue : storedOne.Edge := Serial.rightEdge _ _ ⟨false,⟨true,(0 : Fin 1)⟩⟩

theorem stored_one_label : storedOne.edgeLabel storedOneValue = primitiveLabel 0 (.operation (.const (.nat 1))) := rfl

theorem stored_one_attachment :
    storedOne.target (Serial.leftEdge _ _ ⟨.share,(1 : Fin 3)⟩) = storedOne.source storedOneValue := rfl

/-- No shortcut removes D-term-1-2: its weakening and both contractions are present. -/
theorem canonical_copy_edges (d : Nat) :
    (after (ContractionTree.canonical .atom 1) d).edgeLabel ⟨.share,(0 : Fin 3)⟩ = primitiveLabel d (.weakening .term) ∧
    (after (ContractionTree.canonical .atom 1) d).edgeLabel ⟨.share,(1 : Fin 3)⟩ = primitiveLabel d (.contraction .term) ∧
    (after (ContractionTree.canonical .atom 1) d).edgeLabel ⟨.share,(2 : Fin 3)⟩ = primitiveLabel d (.contraction .term) :=
  ⟨rfl,rfl,rfl⟩
end Hypernets.Copying.Dereference
