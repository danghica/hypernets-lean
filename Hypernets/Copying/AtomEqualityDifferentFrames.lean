import Hypernets.Copying.AtomEqualitySameFrames

/-! Literal distinct-store equality frames with two consumed instances. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Different
open Graph

def inputs (n m : Nat) : List Wire := .term :: List.replicate (n+m) .atom
def treeHole (h : Nat) (name : Nat) : Hole := ⟨name,List.replicate (h+1) .atom,[.atom]⟩
inductive BeforeEdge where
  | compare | left | right | tree | store | treeRight | storeRight
  deriving DecidableEq
inductive AfterEdge where
  | result | discardLeft | discardRight | left | right | tree | store | treeRight | storeRight
  deriving DecidableEq

def inputPort (n m : Nat) {V : Type} (i : Fin (n+m+1)) : Port V (inputs n m).length 2 :=
  .input ⟨i.val,by simp [inputs]⟩
def leftInputs (n m : Nat) {V : Type} : List (Port V (inputs n m).length 2) :=
  (List.finRange n).map (fun i => inputPort n m ⟨i.val+1,by omega⟩)
def rightInputs (n m : Nat) {V : Type} : List (Port V (inputs n m).length 2) :=
  (List.finRange m).map (fun i => inputPort n m ⟨n+i.val+1,by omega⟩)
theorem leftInputs_nodup (n m : Nat) {V : Type} : (leftInputs n m (V := V)).Nodup :=
  nodup_map_on (finRange_nodup n) (fun _ _ _ _ eq => Fin.ext (by have := congrArg Fin.val (Port.input.inj eq); simp [inputPort] at this; omega))
theorem rightInputs_nodup (n m : Nat) {V : Type} : (rightInputs n m (V := V)).Nodup :=
  nodup_map_on (finRange_nodup m) (fun _ _ _ _ eq => Fin.ext (by have := congrArg Fin.val (Port.input.inj eq); simp [inputPort] at this; omega))
@[simp] theorem mem_leftInputs (n m : Nat) {V : Type} (v : Port V (inputs n m).length 2) :
    v ∈ leftInputs n m ↔ ∃ i : Fin n, v = inputPort n m ⟨i.val+1,by omega⟩ := by simp [leftInputs,eq_comm]
@[simp] theorem mem_rightInputs (n m : Nat) {V : Type} (v : Port V (inputs n m).length 2) :
    v ∈ rightInputs n m ↔ ∃ i : Fin m, v = inputPort n m ⟨n+i.val+1,by omega⟩ := by simp [rightInputs,eq_comm]

def beforeLabel (n m : Nat) : BeforeEdge → Primitive
  | .compare => .operation (.binary .atomEq)
  | .left => .instanceEdge
  | .right => .instanceEdge
  | .tree => .hole (treeHole n 0)
  | .treeRight => .hole (treeHole m 1)
  | .storeRight => .store
  | .store => .store

def beforeSource (n m : Nat) : BeforeEdge → List (Port (Fin 6) (inputs n m).length 2)
  | .compare => [inputPort n m 0]
  | .left => [.internal 0]
  | .right => [.internal 1]
  | .tree => .internal 2 :: leftInputs n m
  | .treeRight => .internal 3 :: rightInputs n m
  | .storeRight => [.internal 5]
  | .store => [.internal 4]

def beforeTarget (n m : Nat) : BeforeEdge → List (Port (Fin 6) (inputs n m).length 2)
  | .compare => [.internal 0,.internal 1]
  | .left => [.internal 2]
  | .right => [.internal 3]
  | .tree => [.internal 4]
  | .treeRight => [.internal 5]
  | .storeRight => [.output 1]
  | .store => [.output 0]

def beforeFrame (n m : Nat) : Net primitiveSignature (inputs n m) [.term,.term] where
  Internal := Fin 6
  Edge := BeforeEdge
  finiteInternal := Enumeration.fin 6
  finiteEdge := ⟨[.compare,.left,.right,.tree,.store,.treeRight,.storeRight],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val < 2 then .term else .atom
  edgeLabel := beforeLabel n m
  source := beforeSource n m
  target := beforeTarget n m
  source_nodup e := by cases e <;> simp [beforeSource,leftInputs_nodup,rightInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [beforeTarget]
  source_unique := by
    intro v e f he hf; cases e <;> cases f <;> simp_all [beforeSource,inputPort]
    all_goals
      rcases he with rfl | ⟨i,rfl⟩ <;> simp_all
      obtain ⟨j,eq⟩ := hf
      omega
  target_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [beforeTarget]
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.treeRight,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.storeRight,by simp [beforeSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      by_cases z : i.val = 0
      · have eq : i = ⟨0,by simp [inputs]⟩ := Fin.ext z
        subst i; exact ⟨.compare,by simp [beforeSource,inputPort]⟩
      · by_cases l : i.val ≤ n
        · exact ⟨.tree,by simp [beforeSource]; exact ⟨⟨i.val-1,by omega⟩,by congr 1; apply Fin.ext; simp [inputPort]; omega⟩⟩
        · have hi := i.isLt
          simp only [inputs,List.length_cons,List.length_replicate] at hi
          exact ⟨.treeRight,by simp [beforeSource]; exact ⟨⟨i.val-n-1,by omega⟩,by congr 1; apply Fin.ext; simp [inputPort]; omega⟩⟩
    | output i => simp [Port.IsOutput]; intro e; cases e <;> simp [beforeSource,inputPort]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.compare,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.compare,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.treeRight,by simp [beforeTarget]⟩
    | input i => simp [Port.IsInput]; intro e; cases e <;> simp [beforeTarget]
    | output i =>
      have eq : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        have hi := i.isLt
        change i.val < 2 at hi
        have vals : i.val = 0 ∨ i.val = 1 := by omega
        rcases vals with a | a
        · exact Or.inl (Fin.ext a)
        · exact Or.inr (Fin.ext a)
      rcases eq with rfl | rfl
      · simp [Port.IsInput]; exact ⟨.store,by simp [beforeTarget]⟩
      · simp [Port.IsInput]; exact ⟨.storeRight,by simp [beforeTarget]⟩
  source_typed e := by
    cases e <;> simp [beforeLabel,beforeSource,primitiveSignature,treeHole,inputs,leftInputs,rightInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ,ShareSort.wire]
    all_goals decide
  target_typed e := by
    cases e <;> simp [beforeLabel,beforeTarget,primitiveSignature,treeHole,Operation.outputs,Port.label,ShareSort.wire]
    all_goals decide

def afterLabel (n m : Nat) : AfterEdge → Primitive
  | .result => .operation (.const (.bool false))
  | .discardLeft => .weakening .term
  | .discardRight => .weakening .term
  | .left => .instanceEdge
  | .right => .instanceEdge
  | .tree => .hole (treeHole n 0)
  | .treeRight => .hole (treeHole m 1)
  | .storeRight => .store
  | .store => .store

def afterSource (n m : Nat) : AfterEdge → List (Port (Fin 6) (inputs n m).length 2)
  | .result => [inputPort n m 0]
  | .discardLeft => []
  | .discardRight => []
  | .left => [.internal 0]
  | .right => [.internal 1]
  | .tree => .internal 2 :: leftInputs n m
  | .treeRight => .internal 3 :: rightInputs n m
  | .storeRight => [.internal 5]
  | .store => [.internal 4]

def afterTarget (n m : Nat) : AfterEdge → List (Port (Fin 6) (inputs n m).length 2)
  | .result => []
  | .discardLeft => [.internal 0]
  | .discardRight => [.internal 1]
  | .left => [.internal 2]
  | .right => [.internal 3]
  | .tree => [.internal 4]
  | .treeRight => [.internal 5]
  | .storeRight => [.output 1]
  | .store => [.output 0]

def afterFrame (n m : Nat) : Net primitiveSignature (inputs n m) [.term,.term] where
  Internal := Fin 6
  Edge := AfterEdge
  finiteInternal := Enumeration.fin 6
  finiteEdge := ⟨[.result,.discardLeft,.discardRight,.left,.right,.tree,.store,.treeRight,.storeRight],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val < 2 then .term else .atom
  edgeLabel := afterLabel n m
  source := afterSource n m
  target := afterTarget n m
  source_nodup e := by cases e <;> simp [afterSource,leftInputs_nodup,rightInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [afterTarget]
  source_unique := by
    intro v e f he hf; cases e <;> cases f <;> simp_all [afterSource,inputPort]
    all_goals
      rcases he with rfl | ⟨i,rfl⟩ <;> simp_all
      obtain ⟨j,eq⟩ := hf
      omega
  target_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [afterTarget]
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.treeRight,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.storeRight,by simp [afterSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      by_cases z : i.val = 0
      · have eq : i = ⟨0,by simp [inputs]⟩ := Fin.ext z
        subst i; exact ⟨.result,by simp [afterSource,inputPort]⟩
      · by_cases l : i.val ≤ n
        · exact ⟨.tree,by simp [afterSource]; exact ⟨⟨i.val-1,by omega⟩,by congr 1; apply Fin.ext; simp [inputPort]; omega⟩⟩
        · have hi := i.isLt
          simp only [inputs,List.length_cons,List.length_replicate] at hi
          exact ⟨.treeRight,by simp [afterSource]; exact ⟨⟨i.val-n-1,by omega⟩,by congr 1; apply Fin.ext; simp [inputPort]; omega⟩⟩
    | output i => simp [Port.IsOutput]; intro e; cases e <;> simp [afterSource,inputPort]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.discardLeft,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.discardRight,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.treeRight,by simp [afterTarget]⟩
    | input i => simp [Port.IsInput]; intro e; cases e <;> simp [afterTarget]
    | output i =>
      have eq : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        have hi := i.isLt
        change i.val < 2 at hi
        have vals : i.val = 0 ∨ i.val = 1 := by omega
        rcases vals with a | a
        · exact Or.inl (Fin.ext a)
        · exact Or.inr (Fin.ext a)
      rcases eq with rfl | rfl
      · simp [Port.IsInput]; exact ⟨.store,by simp [afterTarget]⟩
      · simp [Port.IsInput]; exact ⟨.storeRight,by simp [afterTarget]⟩
  source_typed e := by
    cases e <;> simp [afterLabel,afterSource,primitiveSignature,treeHole,inputs,leftInputs,rightInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ,ShareSort.wire]
    all_goals decide
  target_typed e := by
    cases e <;> simp [afterLabel,afterTarget,primitiveSignature,treeHole,Operation.outputs,Port.label,ShareSort.wire]
    all_goals decide
end Hypernets.Copying.AtomEquality.Different
