import Hypernets.Copying.AllocationStoreExamples

/-! Literal Figure 19(b) wiring frames. Other atom references remain exposed;
the tree and term distributor are filled with actual finite graphs below. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

def inputs (h : Nat) : List Wire := .term :: List.replicate h .atom

def treeHole (h : Nat) : Hole := ⟨0,List.replicate (h+1) .atom,[.atom]⟩
def shareHole : Hole := ⟨1,[.term,.term],[.term]⟩

inductive BeforeEdge where
  | reader | inst | tree | store
  deriving DecidableEq
inductive AfterEdge where
  | discard | inst | tree | store | share
  deriving DecidableEq

def inputPort (h : Nat) {V : Type} (i : Fin (h+1)) : Port V (inputs h).length 1 :=
  .input ⟨i.val,by simpa [inputs] using i.isLt⟩

def otherInputs (h : Nat) {V : Type} : List (Port V (inputs h).length 1) :=
  (List.finRange h).map (fun i => inputPort h i.succ)

theorem otherInputs_nodup (h : Nat) {V : Type} : (otherInputs h (V := V)).Nodup :=
  nodup_map_on (finRange_nodup h) (fun _ _ _ _ eq => Fin.ext (by have := congrArg (fun v => v.val) (Port.input.inj eq); simpa [inputPort] using this))

@[simp] theorem mem_otherInputs (h : Nat) {V : Type} (v : Port V (inputs h).length 1) :
    v ∈ otherInputs h ↔ ∃ i : Fin h, v = inputPort h i.succ := by
  simp [otherInputs,eq_comm]

def beforeLabel (h : Nat) : BeforeEdge → Primitive
  | .reader => .operation (.unary .deref)
  | .inst => .instanceEdge
  | .tree => .hole (treeHole h)
  | .store => .store

def beforeSource (h : Nat) : BeforeEdge → List (Port (Fin 3) (inputs h).length 1)
  | .reader => [inputPort h 0]
  | .inst => [.internal 0]
  | .tree => .internal 1 :: otherInputs h
  | .store => [.internal 2]

def beforeTarget {h : Nat} : BeforeEdge → List (Port (Fin 3) (inputs h).length 1)
  | .reader => [.internal 0]
  | .inst => [.internal 1]
  | .tree => [.internal 2]
  | .store => [.output 0]

/-- A reading instance and all other atom inputs meet the same tree and store. -/
def beforeFrame (h : Nat) : Net primitiveSignature (inputs h) [.term] where
  Internal := Fin 3
  Edge := BeforeEdge
  finiteInternal := Enumeration.fin 3
  finiteEdge := ⟨[.reader,.inst,.tree,.store],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val = 0 then .term else .atom
  edgeLabel := beforeLabel h
  source := beforeSource h
  target := beforeTarget
  source_nodup e := by cases e <;> simp [beforeSource,otherInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [beforeTarget]
  source_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all [beforeSource,inputPort]
  target_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all [beforeTarget]
  source_coverage := by
    intro v
    cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [beforeSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let j : Fin (h+1) := ⟨i.val,by simpa [inputs] using i.isLt⟩
      change ∃ e, inputPort h j ∈ beforeSource h e
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ⟨.reader,by simp [beforeSource]⟩
      · exact ⟨.tree,by simp [beforeSource]; exact Or.inr ⟨k,rfl⟩⟩
    | output i => simp [Port.IsOutput,beforeSource]; intro e; cases e <;> simp [beforeSource,inputPort]
  target_coverage := by
    intro v
    cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.reader,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [beforeTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [beforeTarget]⟩
    | input i => simp [Port.IsInput,beforeTarget]; intro e; cases e <;> simp [beforeTarget]
    | output i =>
      have hi : i = (0 : Fin 1) := by apply Fin.ext; change i.val = 0; have := i.isLt; change i.val < 1 at this; omega
      subst i; simp [Port.IsInput]; exact ⟨.store,by simp [beforeTarget]⟩
  source_typed e := by
    cases e <;> simp [beforeLabel,beforeSource,primitiveSignature,treeHole,inputs,otherInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ]
  target_typed e := by
    cases e <;> simp [beforeLabel,beforeTarget,primitiveSignature,treeHole,Operation.outputs,Port.label]

def afterLabel (h : Nat) : AfterEdge → Primitive
  | .discard => .weakening .term
  | .inst => .instanceEdge
  | .tree => .hole (treeHole h)
  | .store => .store
  | .share => .hole shareHole

def afterSource (h : Nat) : AfterEdge → List (Port (Fin 4) (inputs h).length 1)
  | .discard => []
  | .inst => [.internal 0]
  | .tree => .internal 1 :: otherInputs h
  | .store => [.internal 2]
  | .share => [.internal 3,inputPort h 0]

def afterTarget {h : Nat} : AfterEdge → List (Port (Fin 4) (inputs h).length 1)
  | .discard => [.internal 0]
  | .inst => [.internal 1]
  | .tree => [.internal 2]
  | .store => [.internal 3]
  | .share => [.output 0]

/-- The consumed instance is weakened, and store and result feed D-term-1-2. -/
def afterFrame (h : Nat) : Net primitiveSignature (inputs h) [.term] where
  Internal := Fin 4
  Edge := AfterEdge
  finiteInternal := Enumeration.fin 4
  finiteEdge := ⟨[.discard,.inst,.tree,.store,.share],by intro e; cases e <;> simp⟩
  internalLabel i := if i.val = 0 ∨ i.val = 3 then .term else .atom
  edgeLabel := afterLabel h
  source := afterSource h
  target := afterTarget
  source_nodup e := by cases e <;> simp [afterSource,otherInputs_nodup,inputPort]
  target_nodup e := by cases e <;> simp [afterTarget]
  source_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all [afterSource,inputPort]
    · rcases he with rfl | ⟨i,rfl⟩ <;> simp_all
    · rcases hf with rfl | ⟨i,rfl⟩ <;> simp_all
  target_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all [afterTarget]
  source_coverage := by
    intro v
    cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [afterSource]⟩
      · simp only [Port.IsOutput,not_false_eq_true,iff_true]; exact ⟨.share,by simp [afterSource]⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      let j : Fin (h+1) := ⟨i.val,by simpa [inputs] using i.isLt⟩
      change ∃ e, inputPort h j ∈ afterSource h e
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ⟨.share,by simp [afterSource]⟩
      · exact ⟨.tree,by simp [afterSource]; exact Or.inr ⟨k,rfl⟩⟩
    | output i => simp [Port.IsOutput,afterSource]; intro e; cases e <;> simp [afterSource,inputPort]
  target_coverage := by
    intro v
    cases v with
    | internal i =>
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi with rfl | rfl | rfl | rfl
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.discard,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.inst,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.tree,by simp [afterTarget]⟩
      · simp only [Port.IsInput,not_false_eq_true,iff_true]; exact ⟨.store,by simp [afterTarget]⟩
    | input i => simp [Port.IsInput,afterTarget]; intro e; cases e <;> simp [afterTarget]
    | output i =>
      have hi : i = (0 : Fin 1) := by apply Fin.ext; change i.val = 0; have := i.isLt; change i.val < 1 at this; omega
      subst i; simp [Port.IsInput]; exact ⟨.share,by simp [afterTarget]⟩
  source_typed e := by
    cases e <;> simp [afterLabel,afterSource,primitiveSignature,treeHole,shareHole,inputs,otherInputs,inputPort,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ]
    all_goals rfl
  target_typed e := by
    cases e <;> simp [afterLabel,afterTarget,primitiveSignature,treeHole,shareHole,Operation.outputs,Port.label]
    all_goals rfl
end Hypernets.Copying.Dereference
