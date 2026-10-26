import Hypernets.Copying.AtomEqualitySafety

/-! Reference identity is insensitive to arbitrary stored contents, including
identical values and cyclic or nonterminating surrounding graphs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality
open Graph

theorem outcome_serial_left {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) {a b result}
    (out : Outcome G a b result) :
    Outcome (Serial.net G H) (Serial.leftEdge G H a) (Serial.leftEdge G H b) result := by
  obtain ⟨s,t,n,m,left,right,eq⟩ := out
  refine ⟨_,_,n,m,StoreTrace.resolves_serial_left G H left,StoreTrace.resolves_serial_left G H right,eq.trans ?_⟩
  constructor
  · intro same; exact congrArg (Serial.leftEdge G H) same
  · intro same
    cases d <;> exact eq_of_heq (Sigma.mk.inj same).2

namespace Same

theorem arbitrary_contents {h d O} (T : ContractionTree .atom (h+2)) (G : Hypernet d [.term] O) :
    Outcome (Serial.net (before T d) G) (Serial.leftEdge _ _ (beforeLeft T d))
      (Serial.leftEdge _ _ (beforeRight T d)) true := outcome_serial_left _ _ (true_before T d)

theorem noncanonical_run (d : Nat) :
    (machine d (inputs 0) [.term]).Steps 7
      ⟨before (Examples.binaryTree .atom) d,(.search,inputPort 0 0)⟩
      ⟨after (Examples.binaryTree .atom) d,(.backtrack,inputPort 0 0)⟩ := comparison_run _ d
end Same
namespace Different

theorem arbitrary_contents {n m d O} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1))
    (G : Hypernet d [.term,.term] O) :
    Outcome (Serial.net (before T U d) G) (Serial.leftEdge _ _ (beforeLeft T U d))
      (Serial.leftEdge _ _ (beforeRight T U d)) false := outcome_serial_left _ _ (false_before T U d)

theorem contents_cannot_identify_stores {n m d O} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1))
    (G : Hypernet d [.term,.term] O) :
    ¬ Outcome (Serial.net (before T U d) G) (Serial.leftEdge _ _ (beforeLeft T U d))
      (Serial.leftEdge _ _ (beforeRight T U d)) true := by
  intro bad; have eq := outcome_unique (arbitrary_contents T U G) bad; cases eq

/-- Both stores contain the unchanged translation of the same numeral. -/
def identicalContents (value : Nat) : Hypernet 0 [.term,.term] [] :=
  Net.Tensor.net (Allocation.constantArgument value) (Allocation.constantArgument value)

def equalValueHeap (value : Nat) :=
  Serial.net (before (ContractionTree.canonical .atom 1) (ContractionTree.canonical .atom 1) 0)
    (identicalContents value)

def equalValueLeft (value : Nat) : (equalValueHeap value).Edge :=
  Serial.rightEdge _ _ ⟨false,Assignment.literalEdge value⟩
def equalValueRight (value : Nat) : (equalValueHeap value).Edge :=
  Serial.rightEdge _ _ ⟨true,Assignment.literalEdge value⟩

theorem identical_literal_labels (value : Nat) :
    (equalValueHeap value).edgeLabel (equalValueLeft value) = primitiveLabel 0 (.operation (.const (.nat value))) ∧
    (equalValueHeap value).edgeLabel (equalValueRight value) = primitiveLabel 0 (.operation (.const (.nat value))) := ⟨rfl,rfl⟩

theorem identical_literal_attachments (value : Nat) :
    (equalValueHeap value).target (Serial.leftEdge _ _ (beforeStore _ _ 0)) = (equalValueHeap value).source (equalValueLeft value) ∧
    (equalValueHeap value).target (Serial.leftEdge _ _ (beforeStoreRight _ _ 0)) = (equalValueHeap value).source (equalValueRight value) := ⟨rfl,rfl⟩

/-- Equal contents do not imply equal references. -/
theorem identical_contents_compare_false (value : Nat) :
    Outcome (equalValueHeap value) (Serial.leftEdge _ _ (beforeLeft _ _ 0))
      (Serial.leftEdge _ _ (beforeRight _ _ 0)) false := arbitrary_contents _ _ _
end Different
end Hypernets.Copying.AtomEquality
