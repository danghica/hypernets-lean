import Hypernets.Graph.Search
import Hypernets.Graph.Constructors
import Hypernets.Copying.Syntax

/-! The copying alphabet (§§9–10), distinct from the linear UAM alphabet.
Atom sharing is not encoded as term copying. -/
namespace Hypernets.Copying
open Graph

inductive Wire where
  | term | atom | thunk (bound : Nat)
  deriving DecidableEq

/-- Only terms and atoms admit contraction and weakening, never thunk wires. -/
inductive ShareSort where
  | term | atom
  deriving DecidableEq

def ShareSort.wire : ShareSort → Wire
  | .term => .term
  | .atom => .atom

/-- The entire operation set O^ex, including operations absent from the example. -/
inductive Operation where
  | const (c : Constant)
  | lam | app
  | unary (o : Unary)
  | binary (o : Binary)
  deriving DecidableEq

def Operation.kind : Operation → Linear.OperationKind
  | .const _ | .lam => .passive
  | .app | .unary _ | .binary _ => .active

def Operation.outputs : Operation → List Wire
  | .const _ => []
  | .lam => [.thunk 1]
  | .app | .binary _ => [.term, .term]
  | .unary _ => [.term]

structure Hole where
  name : Nat
  input : List Wire
  output : List Wire
  deriving DecidableEq

/-- Store and instance have opposite interfaces. There is no linear variable edge. -/
inductive Primitive where
  | operation (o : Operation)
  | contraction (sort : ShareSort)
  | weakening (sort : ShareSort)
  | instanceEdge
  | store
  | focus (mode : Focus)
  | hole (h : Hole)

def primitiveSignature : Signature Wire Primitive where
  input
    | .operation _ | .instanceEdge | .focus _ => [.term]
    | .contraction s => [s.wire, s.wire]
    | .weakening _ => []
    | .store => [.atom]
    | .hole h => h.input
  output
    | .operation o => o.outputs
    | .contraction s | .weakening s => [s.wire]
    | .instanceEdge => [.atom]
    | .store | .focus _ => [.term]
    | .hole h => h.output

/-- Ordered outputs of a term judgement: variables precede atoms. -/
def environmentInterface (variables atoms : Nat) : List Wire :=
  List.replicate variables .term ++ List.replicate atoms .atom

structure Alphabet where
  Symbol : Type 1
  signature : Signature Wire Symbol

/-- Box bodies expose bound variables first, then free variables and free atoms. -/
structure Box (A : Alphabet) where
  bound : Nat
  freeVariables : Nat
  freeAtoms : Nat
  body : Net A.signature [.term] (environmentInterface (bound + freeVariables) freeAtoms)

def baseAlphabet : Alphabet where
  Symbol := ULift.{1} Primitive
  signature := {
    input p := primitiveSignature.input p.down
    output p := primitiveSignature.output p.down
  }

def nextAlphabet (A : Alphabet) : Alphabet where
  Symbol := Primitive ⊕ Box A
  signature := {
    input
      | .inl p => primitiveSignature.input p
      | .inr b => [.thunk b.bound]
    output
      | .inl p => primitiveSignature.output p
      | .inr b => environmentInterface b.freeVariables b.freeAtoms
  }

@[reducible] def alphabet : Nat → Alphabet
  | 0 => baseAlphabet
  | n+1 => nextAlphabet (alphabet n)

abbrev Hypernet (depth : Nat) (I O : List Wire) := Net (alphabet depth).signature I O

def primitiveLabel : (d : Nat) → Primitive → (alphabet d).Symbol
  | 0, p => .up p
  | _+1, p => .inl p

@[simp] theorem primitive_input (d : Nat) (p : Primitive) :
    (alphabet d).signature.input (primitiveLabel d p) = primitiveSignature.input p := by
  cases d <;> rfl

@[simp] theorem primitive_output (d : Nat) (p : Primitive) :
    (alphabet d).signature.output (primitiveLabel d p) = primitiveSignature.output p := by
  cases d <;> rfl

/-- An actual finite graph for every primitive edge, at any depth allowance. -/
def primitiveNet (d : Nat) (p : Primitive) :
    Hypernet d (primitiveSignature.input p) (primitiveSignature.output p) := by
  simpa using Net.corolla (alphabet d).signature (primitiveLabel d p)

def IsOperation : (d : Nat) → (alphabet d).Symbol → Prop
  | 0, .up (.operation _) => True
  | _+1, .inl (.operation _) => True
  | _, _ => False

/-- The generic operation-path uniqueness proof still applies: operations have
one source even though contraction edges have two. -/
theorem unary_operations {d I O} (G : Hypernet d I O) : G.UnaryOperations (IsOperation d) := by
  intro e he
  rw [G.source_length]
  cases d with
  | zero =>
    cases label : G.edgeLabel e with
    | up p => cases p <;> simp_all [IsOperation, alphabet, baseAlphabet, primitiveSignature]
  | succ n =>
    cases label : G.edgeLabel e with
    | inl p => cases p <;> simp_all [IsOperation, alphabet, nextAlphabet, primitiveSignature]
    | inr b => simp [IsOperation, label] at he

theorem operation_path_unique {d I O} (G : Hypernet d I O)
    {v : G.Vertex} {es fs : List G.Edge} {i j : Fin I.length}
    (h : G.OperationPath (IsOperation d) (.input i) es v)
    (h' : G.OperationPath (IsOperation d) (.input j) fs v) : es = fs ∧ i = j :=
  G.operationPath_unique_from_inputs (IsOperation d) (unary_operations G) h h'

/-- The forward direction of an operation-only path cannot use a sharing edge. -/
theorem contraction_not_operation (d : Nat) (s : ShareSort) :
    ¬ IsOperation d (primitiveLabel d (.contraction s)) := by cases d <;> simp [IsOperation, primitiveLabel]

/-- A box is an actual singleton-edge graph with its recursively typed body. -/
@[reducible] def box {d bound freeVariables freeAtoms}
    (body : Hypernet d [.term] (environmentInterface (bound + freeVariables) freeAtoms)) :
    Hypernet (d+1) [.thunk bound] (environmentInterface freeVariables freeAtoms) :=
  Net.corolla (nextAlphabet (alphabet d)).signature
    (.inr ⟨bound, freeVariables, freeAtoms, body⟩)

/-- Increase only the representation allowance; recursively preserve atom interfaces. -/
def raise : (d : Nat) → {I O : List Wire} → Hypernet d I O → Hypernet (d+1) I O
  | 0, _, _, G => G.relabel _ (fun p => .inl p.down) (fun _ => rfl) (fun _ => rfl)
  | n+1, _, _, G => G.relabel _
      (fun p => match p with
        | .inl o => .inl o
        | .inr b => .inr ⟨b.bound, b.freeVariables, b.freeAtoms, raise n b.body⟩)
      (by intro p; cases p <;> rfl)
      (by intro p; cases p <;> rfl)

theorem raise_source (d : Nat) {I O} (G : Hypernet d I O) :
    HEq (raise d G).source G.source := by cases d <;> rfl

theorem raise_target (d : Nat) {I O} (G : Hypernet d I O) :
    HEq (raise d G).target G.target := by cases d <;> rfl

/-- Deep occurrences distinguish equal-labelled boxes at different edges. -/
def AllEdge : (d : Nat) → {I O : List Wire} → Hypernet d I O → Type
  | 0, _, _, G => G.Edge
  | n+1, _, _, G => G.Edge ⊕ (Σ e : G.Edge, match G.edgeLabel e with
      | .inl _ => Empty
      | .inr b => AllEdge n b.body)

/-- All occurrences, including those in boxes, form an explicitly finite carrier. -/
def allEdgesFinite : (d : Nat) → {I O : List Wire} → (G : Hypernet d I O) →
    Enumeration (AllEdge d G)
  | 0, _, _, G => G.finiteEdge
  | n+1, _, _, G => G.finiteEdge.sum (G.finiteEdge.sigma fun e =>
      match G.edgeLabel e with
      | .inl _ => Enumeration.empty
      | .inr b => allEdgesFinite n b.body)

theorem every_edge_enumerated (d : Nat) {I O} (G : Hypernet d I O) (e : AllEdge d G) :
    e ∈ (allEdgesFinite d G).elements := (allEdgesFinite d G).complete e

end Hypernets.Copying
