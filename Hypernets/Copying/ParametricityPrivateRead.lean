import Hypernets.Copying.ParametricityReadPrefix
import Hypernets.Copying.ParametricityReadTail
import Hypernets.Copying.SharingReadSource

/-! The private store's complete read match after duplicating its instance.
All three actual atom contractions are selected, while their unused sibling
attachments remain in the original complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateRead
open Graph Combined Opening
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

def tail : Hypernet d [.atom] [] :=
  Serial.net (Serial.net (CanonicalTree.atDepth .atom 1 d) (primitiveNet d .store)) (ReadTail.numeral d)

def before : Hypernet d (List.replicate (n+1) .term) [] :=
  Serial.net (ReaderPrefix.net (CopyRule.before (k := 0) (h := 1) T (primitiveNet d .instanceEdge))) (tail d)
def ready : Hypernet d (List.replicate (n+1) .term) [] :=
  Serial.net (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet d .instanceEdge))) (tail d)

def reader : (ready T d).Edge := by cases d <;> exact ⟨false,⟨false,(0 : Fin 1)⟩⟩
def copyEdge (e : (CopyRule.after (k := 0) (h := 1) T (primitiveNet d .instanceEdge)).Edge) : (ready T d).Edge := by
  cases d <;> exact ⟨false,⟨true,e⟩⟩
def instanceEdge : (ready T d).Edge := by
  cases d <;> exact copyEdge T _ ⟨false,⟨false,(0 : Fin 1)⟩⟩
def newShare (i : Fin 3) : (ready T d).Edge := by
  cases d <;> exact copyEdge T _ ⟨true,⟨true,⟨(0 : Fin 1),i⟩⟩⟩
def oldShare (i : Fin 2) : (ready T d).Edge := by
  cases d <;> exact ⟨true,⟨false,⟨false,i⟩⟩⟩
def store : (ready T d).Edge := by
  cases d <;> exact ⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩
def one : (ready T d).Edge := by
  cases d <;> exact ⟨true,⟨true,(0 : Fin 1)⟩⟩

def atomEdges (i : Fin 3) : (ready T d).Edge :=
  if i.val = 0 then newShare T d 2 else if i.val = 1 then newShare T d 1 else oldShare T d 1

theorem atom_label (i : Fin 3) :
    (ready T d).edgeLabel (atomEdges T d i) = primitiveLabel d (.contraction .atom) := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> cases d <;> rfl

def atomPath (i : Fin 4) : (ready T d).Vertex :=
  if zero : i.val = 0 then
    (ready T d).targetPort (instanceEdge T d) ⟨0,by cases d <;> change 0 < 1 <;> decide⟩ else
    (ready T d).targetPort (atomEdges T d ⟨i.val-1,by omega⟩)
      ⟨0,by rw [atom_label,primitive_output]; decide⟩
def atomSides (i : Fin 3) : (ready T d).Vertex :=
  (ready T d).sourcePort (atomEdges T d i)
    ⟨if i.val = 0 then 1 else 0,by rw [atom_label,primitive_input]; split <;> decide⟩
def orientation (i : Fin 3) : Bool := i.val != 0

/-- The observed source path crosses the new atom distributor and then the
original D₁,₁ at the allocated cell; no atom wire is contracted away. -/
theorem atom_source (i : Fin 3) :
    (ready T d).source (atomEdges T d i) = if orientation i then
      [atomSides T d i,atomPath T d ⟨i.val,by omega⟩]
    else [atomPath T d ⟨i.val,by omega⟩,atomSides T d i] := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> cases d <;> rfl

theorem atom_target (i : Fin 3) :
    (ready T d).target (atomEdges T d i) = [atomPath T d ⟨i.val+1,by omega⟩] := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> cases d <;> rfl

theorem atom_injective : Function.Injective (atomEdges T d) := by
  intro i j eq
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> try rfl
  all_goals cases d
  all_goals try solve | cases congrArg Sigma.fst eq
  all_goals
    have inner := eq_of_heq (Sigma.mk.inj eq).2
    have inner := eq_of_heq (Sigma.mk.inj inner).2
    have inner := eq_of_heq (Sigma.mk.inj inner).2
    have inner := eq_of_heq (Sigma.mk.inj inner).2
    have inner := eq_of_heq (Sigma.mk.inj inner).2
    have value := congrArg Fin.val inner
    contradiction

noncomputable def treeOccurrence : Occurrence
    (ContractionSpine.atDepth .atom 2 orientation d) (ready T d) :=
  ContractionSpine.occurrence (ready T d) .atom 2 orientation (atomEdges T d)
    (atomPath T d) (atomSides T d) (atom_injective T d) (atom_label T d)
    (atom_source T d) (atom_target T d)

def argument : (ready T d).Vertex := by
  cases d <;> exact BoundarySerial.leftInsert _ _ (ReaderPrefix.active (CopyRule.after (k := 0) (h := 1) T (primitiveNet _ .instanceEdge)))
def storeValue : (ready T d).Vertex :=
  (ready T d).targetPort (store T d) ⟨0,by cases d <;> change 0 < 1 <;> decide⟩

theorem reader_label : (ready T d).edgeLabel (reader T d) = primitiveLabel d (.operation (.unary .deref)) := by
  cases d <;> rfl
theorem instance_label : (ready T d).edgeLabel (instanceEdge T d) = primitiveLabel d .instanceEdge := by
  cases d <;> rfl
theorem store_label : (ready T d).edgeLabel (store T d) = primitiveLabel d .store := by cases d <;> rfl

theorem reader_source : (ready T d).source (reader T d) = [.input ⟨0,by simp⟩] := by
  cases d with
  | zero =>
    apply congrArg List.singleton
    change BoundarySerial.leftInsert (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet 0 .instanceEdge)))
      (tail 0) (Port.map Sum.inl ((ReaderPrefix.pattern 0 n (environmentInterface 0 1)).sourcePort false (0 : Fin 1))) = _
    simp only [Net.sourcePort,ReaderPrefix.pattern,ReaderPrefix.frame,ReaderPrefix.source,Net.relabel,Port.map]
    exact left_input _ _ _
  | succ d =>
    apply congrArg List.singleton
    change BoundarySerial.leftInsert (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet (d+1) .instanceEdge)))
      (tail (d+1)) (Port.map Sum.inl ((ReaderPrefix.pattern (d+1) n (environmentInterface 0 1)).sourcePort false (0 : Fin 1))) = _
    simp only [Net.sourcePort,ReaderPrefix.pattern,ReaderPrefix.frame,ReaderPrefix.source,Net.relabel,Port.map]
    exact left_input _ _ _
theorem reader_target : (ready T d).target (reader T d) = [argument T d] := by cases d <;> rfl
theorem instance_source : (ready T d).source (instanceEdge T d) = [argument T d] := by
  cases d with
  | zero =>
    apply congrArg List.singleton
    change BoundarySerial.leftInsert (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet 0 .instanceEdge))) (tail 0)
      (Net.Expansion.insert (ReaderPrefix.pattern 0 n (environmentInterface 0 1))
        (ReaderPrefix.filling (CopyRule.after (k := 0) (h := 1) T (primitiveNet 0 .instanceEdge))) true
        (BoundarySerial.leftInsert _ _ (CopyRule.pairInsert (k := 0) (h := 1) T (primitiveNet 0 .instanceEdge) false (.input (0 : Fin 1))))) = _
    rw [CopyRule.pair_left_input,left_input]
    rfl
  | succ d =>
    apply congrArg List.singleton
    change BoundarySerial.leftInsert (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet (d+1) .instanceEdge))) (tail (d+1))
      (Net.Expansion.insert (ReaderPrefix.pattern (d+1) n (environmentInterface 0 1))
        (ReaderPrefix.filling (CopyRule.after (k := 0) (h := 1) T (primitiveNet (d+1) .instanceEdge))) true
        (BoundarySerial.leftInsert _ _ (CopyRule.pairInsert (k := 0) (h := 1) T (primitiveNet (d+1) .instanceEdge) false (.input (0 : Fin 1))))) = _
    rw [CopyRule.pair_left_input,left_input]
    rfl
theorem instance_target : (ready T d).target (instanceEdge T d) = [atomPath T d 0] := by cases d <;> rfl
theorem store_source : (ready T d).source (store T d) = [atomPath T d 3] := by cases d <;> rfl
theorem store_target : (ready T d).target (store T d) = [storeValue T d] := by cases d <;> rfl

/-- Complete occurrence of the original dereference rule, with the real
private store and the exact ordered three-contraction atom spine. -/
noncomputable def readOccurrence : Occurrence
    (Dereference.before (ContractionSpine.tree .atom 2 orientation) d) (ready T d) :=
  (Occurrence.ofIso (Dereference.Context.graphIso (ContractionSpine.tree .atom 2 orientation)).symm).comp
    (Dereference.Context.occurrence (ready T d) (treeOccurrence T d)
      (reader T d) (instanceEdge T d) (store T d)
      (reader_label T d) (instance_label T d) (store_label T d)
      (.input ⟨0,by simp⟩) (argument T d) (atomPath T d 0) (atomPath T d 3) (storeValue T d)
      (reader_source T d) (reader_target T d) (instance_source T d) (instance_target T d)
      (store_source T d) (store_target T d) rfl rfl (fun i => .inr (.inl (atom_label T d i))))

end Hypernets.Copying.Parametricity.PrivateRead
