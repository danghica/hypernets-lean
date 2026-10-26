import Hypernets.Copying.CopyExamples

/-! Literal assignment frames: preserve the selected store and all other atom
inputs, reconnect the new value, and explicitly weaken the old contents. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

def inputs (h : Nat) : List Wire := .term :: List.replicate h .atom
def outputs (O : List Wire) : List Wire := .term :: O
def treeHole (h : Nat) : Hole := ⟨0,List.replicate (h+1) .atom,[.atom]⟩
def valueHole (O : List Wire) : Hole := ⟨1,[.term],O⟩

inductive BeforeEdge where
  | assign | inst | tree | store | value
  deriving DecidableEq
inductive AfterEdge where
  | discardInstance | inst | tree | store | value | discardOld | unit
  deriving DecidableEq

def inputPort (h : Nat) (O : List Wire) {V : Type} (i : Fin (h+1)) : Port V (inputs h).length (outputs O).length :=
  .input ⟨i.val,by simpa [inputs] using i.isLt⟩
def otherInputs (h : Nat) (O : List Wire) {V : Type} : List (Port V (inputs h).length (outputs O).length) :=
  (List.finRange h).map (fun i => inputPort h O i.succ)
def outputPort (h : Nat) (O : List Wire) {V : Type} (i : Fin O.length) : Port V (inputs h).length (outputs O).length :=
  .output i.succ
def valueOutputs (h : Nat) (O : List Wire) {V : Type} : List (Port V (inputs h).length (outputs O).length) :=
  (List.finRange O.length).map (outputPort h O)

theorem otherInputs_nodup (h : Nat) (O : List Wire) {V : Type} : (otherInputs h O (V := V)).Nodup :=
  nodup_map_on (finRange_nodup h) (fun _ _ _ _ eq => Fin.ext (by have := congrArg (fun v => v.val) (Port.input.inj eq); simpa [inputPort] using this))
@[simp] theorem mem_otherInputs (h : Nat) (O : List Wire) {V : Type} (v : Port V (inputs h).length (outputs O).length) :
    v ∈ otherInputs h O ↔ ∃ i : Fin h, v = inputPort h O i.succ := by simp [otherInputs,eq_comm]
theorem valueOutputs_nodup (h : Nat) (O : List Wire) {V : Type} : (valueOutputs h O (V := V)).Nodup :=
  nodup_map_on (finRange_nodup O.length) (fun _ _ _ _ eq => Fin.ext (by have q := congrArg Fin.val (Port.output.inj eq); simpa using q))
@[simp] theorem mem_valueOutputs (h : Nat) (O : List Wire) {V : Type} (v : Port V (inputs h).length (outputs O).length) :
    v ∈ valueOutputs h O ↔ ∃ i : Fin O.length, v = outputPort h O i := by simp [valueOutputs,eq_comm]

def beforeLabel (h : Nat) (O : List Wire) : BeforeEdge → Primitive
  | .assign => .operation (.binary .assign)
  | .inst => .instanceEdge
  | .tree => .hole (treeHole h)
  | .store => .store
  | .value => .hole (valueHole O)

def beforeSource (h : Nat) (O : List Wire) : BeforeEdge → List (Port (Fin 4) (inputs h).length (outputs O).length)
  | .assign => [inputPort h O 0]
  | .inst => [.internal 0]
  | .tree => .internal 2 :: otherInputs h O
  | .store => [.internal 3]
  | .value => [.internal 1]

def beforeTarget (h : Nat) (O : List Wire) : BeforeEdge → List (Port (Fin 4) (inputs h).length (outputs O).length)
  | .assign => [.internal 0,.internal 1]
  | .inst => [.internal 2]
  | .tree => [.internal 3]
  | .store => [.output ⟨0,by simp [outputs]⟩]
  | .value => valueOutputs h O

def beforeFrame (h : Nat) (O : List Wire) : Net primitiveSignature (inputs h) (outputs O) where
  Internal := Fin 4
  Edge := BeforeEdge
  finiteInternal := Enumeration.fin 4
  finiteEdge := ⟨[.assign,.inst,.tree,.store,.value],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val < 2 then .term else .atom
  edgeLabel := beforeLabel h O
  source := beforeSource h O
  target := beforeTarget h O
  source_nodup e := by cases e <;> simp [beforeSource,otherInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [beforeTarget,valueOutputs_nodup,outputPort]
  source_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [beforeSource,inputPort]
  target_unique := by
    intro v e f he hf; cases e <;> cases f <;> simp_all [beforeTarget,outputPort,Fin.succ_ne_zero]
    · rcases he with rfl | rfl <;> simp_all
    · obtain ⟨i,eq⟩ := hf
      have bad := congrArg Fin.val eq
      simp at bad
    · rcases hf with rfl | rfl <;> simp_all
    · obtain ⟨i,eq⟩ := he
      have bad := congrArg Fin.val eq
      simp at bad
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.value,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [beforeSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let j : Fin (h+1) := ⟨i.val,by simpa [inputs] using i.isLt⟩
      change ∃ e, inputPort h O j ∈ beforeSource h O e
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ⟨.assign,by simp [beforeSource]⟩
      · exact ⟨.tree,by simp [beforeSource]; exact Or.inr ⟨k,rfl⟩⟩
    | output i => simp [Port.IsOutput,beforeSource]; intro e; cases e <;> simp [beforeSource,inputPort]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.assign,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.assign,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeTarget]⟩
    | input i => simp [Port.IsInput,beforeTarget]; intro e; cases e <;> simp [beforeTarget,outputPort]
    | output i =>
      refine ⟨fun _ => by simp [Port.IsInput],fun _ => ?_⟩
      change ∃ e, Port.output i ∈ beforeTarget h O e
      refine Fin.cases ?_ (fun k => ?_) i
      · exact ⟨.store,by simp [beforeTarget]⟩
      · exact ⟨.value,by simp [beforeTarget,outputPort]⟩
  source_typed e := by
    cases e <;> simp [beforeLabel,beforeSource,primitiveSignature,treeHole,valueHole,inputs,outputs,otherInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ,ShareSort.wire]
    all_goals decide
  target_typed e := by
    cases e <;> simp [beforeLabel,beforeTarget,primitiveSignature,treeHole,valueHole,inputs,outputs,valueOutputs,outputPort,Operation.outputs,Port.label,
      List.map_map,Function.comp_def,ShareSort.wire,List.finRange,List.map_ofFn,List.ofFn_getElem]
    all_goals decide

def afterLabel (h : Nat) (O : List Wire) : AfterEdge → Primitive
  | .discardInstance => .weakening .term
  | .inst => .instanceEdge
  | .tree => .hole (treeHole h)
  | .store => .store
  | .value => .hole (valueHole O)
  | .discardOld => .weakening .term
  | .unit => .operation (.const .unit)

def afterSource (h : Nat) (O : List Wire) : AfterEdge → List (Port (Fin 4) (inputs h).length (outputs O).length)
  | .discardInstance => []
  | .inst => [.internal 0]
  | .tree => .internal 2 :: otherInputs h O
  | .store => [.internal 3]
  | .value => [.internal 1]
  | .discardOld => []
  | .unit => [inputPort h O 0]

def afterTarget (h : Nat) (O : List Wire) : AfterEdge → List (Port (Fin 4) (inputs h).length (outputs O).length)
  | .discardInstance => [.internal 0]
  | .inst => [.internal 2]
  | .tree => [.internal 3]
  | .store => [.internal 1]
  | .value => valueOutputs h O
  | .discardOld => [.output ⟨0,by simp [outputs]⟩]
  | .unit => []

def afterFrame (h : Nat) (O : List Wire) : Net primitiveSignature (inputs h) (outputs O) where
  Internal := Fin 4
  Edge := AfterEdge
  finiteInternal := Enumeration.fin 4
  finiteEdge := ⟨[.discardInstance,.inst,.tree,.store,.value,.discardOld,.unit],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val < 2 then .term else .atom
  edgeLabel := afterLabel h O
  source := afterSource h O
  target := afterTarget h O
  source_nodup e := by cases e <;> simp [afterSource,otherInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [afterTarget,valueOutputs_nodup,outputPort]
  source_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [afterSource,inputPort]
  target_unique := by
    intro v e f he hf; cases e <;> cases f <;> simp_all [afterTarget,outputPort,Fin.succ_ne_zero]
    · obtain ⟨i,eq⟩ := he
      have bad := congrArg Fin.val eq
      simp at bad
    · obtain ⟨i,eq⟩ := hf
      have bad := congrArg Fin.val eq
      simp at bad
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.value,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [afterSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let j : Fin (h+1) := ⟨i.val,by simpa [inputs] using i.isLt⟩
      change ∃ e, inputPort h O j ∈ afterSource h O e
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ⟨.unit,by simp [afterSource]⟩
      · exact ⟨.tree,by simp [afterSource]; exact Or.inr ⟨k,rfl⟩⟩
    | output i => simp [Port.IsOutput,afterSource]; intro e; cases e <;> simp [afterSource,inputPort]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.discardInstance,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterTarget]⟩
    | input i => simp [Port.IsInput,afterTarget]; intro e; cases e <;> simp [afterTarget,outputPort]
    | output i =>
      refine ⟨fun _ => by simp [Port.IsInput],fun _ => ?_⟩
      change ∃ e, Port.output i ∈ afterTarget h O e
      refine Fin.cases ?_ (fun k => ?_) i
      · exact ⟨.discardOld,by simp [afterTarget]⟩
      · exact ⟨.value,by simp [afterTarget,outputPort]⟩
  source_typed e := by
    cases e <;> simp [afterLabel,afterSource,primitiveSignature,treeHole,valueHole,inputs,outputs,otherInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ,ShareSort.wire]
    all_goals decide
  target_typed e := by
    cases e <;> simp [afterLabel,afterTarget,primitiveSignature,treeHole,valueHole,inputs,outputs,valueOutputs,outputPort,Operation.outputs,Port.label,
      List.map_map,Function.comp_def,ShareSort.wire,List.finRange,List.map_ofFn,List.ofFn_getElem]
    all_goals decide
end Hypernets.Copying.Assignment
