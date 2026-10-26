import Hypernets.Copying.AssignmentExamples

/-! Literal same-store equality frames with two consumed instances. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Same
open Graph

def inputs (h : Nat) : List Wire := .term :: List.replicate h .atom
def treeHole (h : Nat) : Hole := ⟨0,List.replicate (h+2) .atom,[.atom]⟩
inductive BeforeEdge where
  | compare | left | right | tree | store
  deriving DecidableEq
inductive AfterEdge where
  | result | discardLeft | discardRight | left | right | tree | store
  deriving DecidableEq

def inputPort (h : Nat) {V : Type} (i : Fin (h+1)) : Port V (inputs h).length 1 :=
  .input ⟨i.val,by simp [inputs]⟩
def otherInputs (h : Nat) {V : Type} : List (Port V (inputs h).length 1) :=
  (List.finRange h).map (fun i => inputPort h i.succ)
theorem otherInputs_nodup (h : Nat) {V : Type} : (otherInputs h (V := V)).Nodup :=
  nodup_map_on (finRange_nodup h) (fun _ _ _ _ eq => Fin.ext (by have := congrArg Fin.val (Port.input.inj eq); simpa [inputPort] using this))
@[simp] theorem mem_otherInputs (h : Nat) {V : Type} (v : Port V (inputs h).length 1) :
    v ∈ otherInputs h ↔ ∃ i : Fin h, v = inputPort h i.succ := by simp [otherInputs,eq_comm]

def beforeLabel (h : Nat) : BeforeEdge → Primitive
  | .compare => .operation (.binary .atomEq)
  | .left => .instanceEdge
  | .right => .instanceEdge
  | .tree => .hole (treeHole h)
  | .store => .store

def beforeSource (h : Nat) : BeforeEdge → List (Port (Fin 5) (inputs h).length 1)
  | .compare => [inputPort h 0]
  | .left => [.internal 0]
  | .right => [.internal 1]
  | .tree => .internal 2 :: .internal 3 :: otherInputs h
  | .store => [.internal 4]

def beforeTarget (h : Nat) : BeforeEdge → List (Port (Fin 5) (inputs h).length 1)
  | .compare => [.internal 0,.internal 1]
  | .left => [.internal 2]
  | .right => [.internal 3]
  | .tree => [.internal 4]
  | .store => [.output 0]

def beforeFrame (h : Nat) : Net primitiveSignature (inputs h) [.term] where
  Internal := Fin 5
  Edge := BeforeEdge
  finiteInternal := Enumeration.fin 5
  finiteEdge := ⟨[.compare,.left,.right,.tree,.store],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val < 2 then .term else .atom
  edgeLabel := beforeLabel h
  source := beforeSource h
  target := beforeTarget h
  source_nodup e := by cases e <;> simp [beforeSource,otherInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [beforeTarget]
  source_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [beforeSource,inputPort]
  target_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [beforeTarget]
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [beforeSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let j : Fin (h+1) := ⟨i.val,by simpa [inputs] using i.isLt⟩
      change ∃ e, inputPort h j ∈ beforeSource h e
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ⟨.compare,by simp [beforeSource]⟩
      · exact ⟨.tree,by simp [beforeSource]; exact Or.inr (Or.inr ⟨k,rfl⟩)⟩
    | output i => simp [Port.IsOutput]; intro e; cases e <;> simp [beforeSource,inputPort]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.compare,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.compare,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeTarget]⟩
    | input i => simp [Port.IsInput]; intro e; cases e <;> simp [beforeTarget]
    | output i =>
      have eq : i = (0 : Fin 1) := by apply Fin.ext; change i.val = 0; have := i.isLt; change i.val < 1 at this; omega
      subst i; simp [Port.IsInput]; exact ⟨.store,by simp [beforeTarget]⟩
  source_typed e := by
    cases e <;> simp [beforeLabel,beforeSource,primitiveSignature,treeHole,inputs,otherInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ,ShareSort.wire]
    all_goals decide
  target_typed e := by
    cases e <;> simp [beforeLabel,beforeTarget,primitiveSignature,treeHole,Operation.outputs,Port.label,ShareSort.wire]
    all_goals decide

def afterLabel (h : Nat) : AfterEdge → Primitive
  | .result => .operation (.const (.bool true))
  | .discardLeft => .weakening .term
  | .discardRight => .weakening .term
  | .left => .instanceEdge
  | .right => .instanceEdge
  | .tree => .hole (treeHole h)
  | .store => .store

def afterSource (h : Nat) : AfterEdge → List (Port (Fin 5) (inputs h).length 1)
  | .result => [inputPort h 0]
  | .discardLeft => []
  | .discardRight => []
  | .left => [.internal 0]
  | .right => [.internal 1]
  | .tree => .internal 2 :: .internal 3 :: otherInputs h
  | .store => [.internal 4]

def afterTarget (h : Nat) : AfterEdge → List (Port (Fin 5) (inputs h).length 1)
  | .result => []
  | .discardLeft => [.internal 0]
  | .discardRight => [.internal 1]
  | .left => [.internal 2]
  | .right => [.internal 3]
  | .tree => [.internal 4]
  | .store => [.output 0]

def afterFrame (h : Nat) : Net primitiveSignature (inputs h) [.term] where
  Internal := Fin 5
  Edge := AfterEdge
  finiteInternal := Enumeration.fin 5
  finiteEdge := ⟨[.result,.discardLeft,.discardRight,.left,.right,.tree,.store],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val < 2 then .term else .atom
  edgeLabel := afterLabel h
  source := afterSource h
  target := afterTarget h
  source_nodup e := by cases e <;> simp [afterSource,otherInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [afterTarget]
  source_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [afterSource,inputPort]
  target_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [afterTarget]
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [afterSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let j : Fin (h+1) := ⟨i.val,by simpa [inputs] using i.isLt⟩
      change ∃ e, inputPort h j ∈ afterSource h e
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ⟨.result,by simp [afterSource]⟩
      · exact ⟨.tree,by simp [afterSource]; exact Or.inr (Or.inr ⟨k,rfl⟩)⟩
    | output i => simp [Port.IsOutput]; intro e; cases e <;> simp [afterSource,inputPort]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.discardLeft,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.discardRight,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.left,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.right,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterTarget]⟩
    | input i => simp [Port.IsInput]; intro e; cases e <;> simp [afterTarget]
    | output i =>
      have eq : i = (0 : Fin 1) := by apply Fin.ext; change i.val = 0; have := i.isLt; change i.val < 1 at this; omega
      subst i; simp [Port.IsInput]; exact ⟨.store,by simp [afterTarget]⟩
  source_typed e := by
    cases e <;> simp [afterLabel,afterSource,primitiveSignature,treeHole,inputs,otherInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ,ShareSort.wire]
    all_goals decide
  target_typed e := by
    cases e <;> simp [afterLabel,afterTarget,primitiveSignature,treeHole,Operation.outputs,Port.label,ShareSort.wire]
    all_goals decide
end Hypernets.Copying.AtomEquality.Same
