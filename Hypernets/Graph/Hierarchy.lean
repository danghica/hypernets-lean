import Hypernets.Graph.PlugIsomorphism
import Hypernets.Graph.OperationPaths
import Hypernets.LocalReasoning

/-!
Finite-depth boxed hypernets with the linear UAM's type discipline (§§4–5).
A box binding `n` variables and exposing `m` has external type
T^n(*) => *^m, while its body has type * => *^(n+m).
Deep edge occurrences have a recursively constructed finite enumeration.
-/

namespace Hypernets.Graph.Net

universe u v

/-- Relabel edges along a signature-preserving map. No incidence changes. -/
@[reducible] def relabel {L : Type} {Op : Type u} {Op' : Type v}
    {σ : Signature L Op} {I O : List L} (G : Net σ I O) (τ : Signature L Op')
    (f : Op → Op') (input : ∀ o, τ.input (f o) = σ.input o)
    (output : ∀ o, τ.output (f o) = σ.output o) : Net τ I O where
  Internal := G.Internal
  Edge := G.Edge
  finiteInternal := G.finiteInternal
  finiteEdge := G.finiteEdge
  internalLabel := G.internalLabel
  edgeLabel e := f (G.edgeLabel e)
  source := G.source
  target := G.target
  source_nodup := G.source_nodup
  target_nodup := G.target_nodup
  source_unique := G.source_unique
  target_unique := G.target_unique
  source_coverage := G.source_coverage
  target_coverage := G.target_coverage
  source_typed e := (G.source_typed e).trans (input _).symm
  target_typed e := (G.target_typed e).trans (output _).symm

end Hypernets.Graph.Net

namespace Hypernets.Linear

open Graph

inductive Wire where
  | term
  | thunk (bound : Nat)
  deriving DecidableEq

/-- Every operation has one term source, a list of term arguments, and a list
of thunks with specified numbers of bound variables (paper §5.1). -/
structure Operations (Op : Type) where
  arguments : Op → Nat
  binders : Op → List Nat

/-- Hole labels are intrinsically typed and may have arbitrary interfaces. -/
structure Hole where
  name : Nat
  input : List Wire
  output : List Wire
  deriving DecidableEq

inductive Primitive (Op : Type) where
  | operation : Op → Primitive Op
  | variable : Primitive Op
  | focus : Focus → Primitive Op
  | hole : Hole → Primitive Op

def primitiveSignature {Op : Type} (ops : Operations Op) : Signature Wire (Primitive Op) where
  input
    | .hole h => h.input
    | _ => [.term]
  output
    | .operation o => List.replicate (ops.arguments o) .term ++ (ops.binders o).map Wire.thunk
    | .variable => [.term]
    | .focus _ => [.term]
    | .hole h => h.output

/-- All layer alphabets live in one fixed universe; graph carriers remain small
finite types. This avoids increasing universes with each nesting level. -/
structure Alphabet where
  Symbol : Type 1
  signature : Signature Wire Symbol

structure Box (A : Alphabet) where
  bound : Nat
  free : Nat
  body : Net A.signature [.term] (List.replicate (bound + free) .term)

def baseAlphabet {Op : Type} (ops : Operations Op) : Alphabet where
  Symbol := ULift.{1} (Primitive Op)
  signature := {
    input p := (primitiveSignature ops).input p.down
    output p := (primitiveSignature ops).output p.down
  }

def nextAlphabet {Op : Type} (ops : Operations Op) (A : Alphabet) : Alphabet where
  Symbol := Primitive Op ⊕ Box A
  signature := {
    input
      | .inl p => (primitiveSignature ops).input p
      | .inr b => [.thunk b.bound]
    output
      | .inl p => (primitiveSignature ops).output p
      | .inr b => List.replicate b.free .term
  }

@[reducible] def alphabet {Op : Type} (ops : Operations Op) : Nat → Alphabet
  | 0 => baseAlphabet ops
  | n + 1 => nextAlphabet ops (alphabet ops n)

abbrev Hypernet {Op : Type} (ops : Operations Op) (depth : Nat) (I O : List Wire) :=
  Net (alphabet ops depth).signature I O

def IsOperation {Op : Type} (ops : Operations Op) :
    (depth : Nat) → (alphabet ops depth).Symbol → Prop
  | 0, p => match p.down with | .operation _ => True | _ => False
  | _ + 1, .inl (.operation _) => True
  | _ + 1, _ => False

theorem unary_operations {Op : Type} (ops : Operations Op) (depth : Nat)
    {I O} (G : Hypernet ops depth I O) : G.UnaryOperations (IsOperation ops depth) := by
  intro e he
  rw [G.source_length]
  cases depth with
  | zero =>
      cases label : G.edgeLabel e with
      | up p => cases p <;> simp_all [IsOperation, alphabet, baseAlphabet, primitiveSignature]
  | succ n =>
      cases label : G.edgeLabel e with
      | inl p => cases p <;> simp_all [IsOperation, alphabet, nextAlphabet, primitiveSignature]
      | inr b => simp [IsOperation, label] at he

/-- Lemma 22's uniqueness conclusion specialized to actual typed hypernets:
there is no additional determinism or locality premise. -/
theorem operation_path_unique {Op : Type} (ops : Operations Op) (depth : Nat)
    {I O} (G : Hypernet ops depth I O)
    {v : G.Vertex} {es fs : List G.Edge} {i j : Fin I.length}
    (h : G.OperationPath (IsOperation ops depth) (.input i) es v)
    (h' : G.OperationPath (IsOperation ops depth) (.input j) fs v) : es = fs ∧ i = j :=
  G.operationPath_unique_from_inputs (IsOperation ops depth) (unary_operations ops depth G) h h'

/-- A concrete boxed hypernet, with the body scope enforced by its type. -/
@[reducible] def box {Op : Type} {ops : Operations Op} {depth bound free : Nat}
    (body : Hypernet ops depth [.term] (List.replicate (bound + free) .term)) :
    Hypernet ops (depth + 1) [.thunk bound] (List.replicate free .term) :=
  Net.corolla (nextAlphabet ops (alphabet ops depth)).signature
    (Sum.inr (⟨bound, free, body⟩ : Box (alphabet ops depth)))

/-- Promote a graph to a larger depth bound, recursively promoting box bodies.
The graph's outer carriers, incidence, and boundary order are unchanged. -/
def raise {Op : Type} (ops : Operations Op) :
    (depth : Nat) → {I O : List Wire} → Hypernet ops depth I O → Hypernet ops (depth + 1) I O
  | 0, _, _, G =>
      G.relabel _ (fun p => .inl p.down) (fun _ => rfl) (fun _ => rfl)
  | n + 1, _, _, G =>
      G.relabel _
        (fun p => match p with
          | .inl o => .inl o
          | .inr b => .inr ⟨b.bound, b.free, raise ops n b.body⟩)
        (by intro p; cases p <;> rfl)
        (by intro p; cases p <;> rfl)

theorem raise_source {Op : Type} (ops : Operations Op) (depth : Nat)
    {I O} (G : Hypernet ops depth I O) :
    HEq (raise ops depth G).source G.source := by cases depth <;> rfl

theorem raise_target {Op : Type} (ops : Operations Op) (depth : Nat)
    {I O} (G : Hypernet ops depth I O) :
    HEq (raise ops depth G).target G.target := by cases depth <;> rfl

/-- Distinct occurrences in different boxes have distinct addresses even if
the box bodies happen to be equal graphs. The left summand is shallow edges. -/
def AllEdge {Op : Type} (ops : Operations Op) :
    (depth : Nat) → {I O : List Wire} → Hypernet ops depth I O → Type
  | 0, _, _, G => G.Edge
  | n + 1, _, _, G => G.Edge ⊕ (Σ e : G.Edge, match G.edgeLabel e with
      | .inl _ => Empty
      | .inr b => AllEdge ops n b.body)

/-- Constructive finite enumeration of all shallow and deep edge occurrences.
This supplies the content of Appendix A, Lemma 19, for the typed hierarchy. -/
def allEdgesFinite {Op : Type} (ops : Operations Op) :
    (depth : Nat) → {I O : List Wire} → (G : Hypernet ops depth I O) →
      Enumeration (AllEdge ops depth G)
  | 0, _, _, G => G.finiteEdge
  | n + 1, _, _, G =>
      G.finiteEdge.sum (G.finiteEdge.sigma fun e =>
        match G.edgeLabel e with
        | .inl _ => Enumeration.empty
        | .inr b => allEdgesFinite ops n b.body)

theorem every_edge_enumerated {Op : Type} (ops : Operations Op) (depth : Nat)
    {I O} (G : Hypernet ops depth I O) (e : AllEdge ops depth G) :
    e ∈ (allEdgesFinite ops depth G).elements :=
  (allEdgesFinite ops depth G).complete e

def primitiveHole {Op : Type} : Primitive Op → Option Hole
  | .hole h => some h
  | _ => none

/-- Read a hole label at a shallow or deep occurrence address. -/
def holeAt {Op : Type} (ops : Operations Op) :
    (depth : Nat) → {I O : List Wire} → (G : Hypernet ops depth I O) →
      AllEdge ops depth G → Option Hole
  | 0, _, _, G, e => primitiveHole (G.edgeLabel e).down
  | _ + 1, _, _, G, .inl e => match G.edgeLabel e with
      | .inl p => primitiveHole p
      | .inr _ => none
  | n + 1, _, _, G, .inr ⟨e, occurrence⟩ => by
      cases label : G.edgeLabel e with
      | inl p =>
          have absent : Empty := by simpa only [label] using occurrence
          exact nomatch absent
      | inr b =>
          exact holeAt ops n b.body (by simpa only [label] using occurrence)

/-- The paper's context condition: a typed hole label occurs at most once at
any depth. The addressed replacement operation does not assume this condition. -/
def UniqueHoles {Op : Type} (ops : Operations Op) (depth : Nat) {I O}
    (G : Hypernet ops depth I O) : Prop :=
  ∀ h (a b : AllEdge ops depth G), holeAt ops depth G a = some h →
    holeAt ops depth G b = some h → a = b

abbrev Context {Op : Type} (ops : Operations Op) (depth : Nat) (I O : List Wire) :=
  {G : Hypernet ops depth I O // UniqueHoles ops depth G}

/-- Boxing preserves uniqueness of hole labels at all depths. A shallow box
edge is not itself a hole, and its child occurrences retain their addresses. -/
theorem box_unique_holes {Op : Type} {ops : Operations Op} {depth bound free : Nat}
    (body : Hypernet ops depth [.term] (List.replicate (bound + free) .term))
    (unique : UniqueHoles ops depth body) :
    UniqueHoles ops (depth + 1) (box (bound := bound) (free := free) body) := by
  intro h a b ha hb
  cases a with
  | inl e =>
      change (none : Option Hole) = some h at ha
      cases ha
  | inr a =>
      cases b with
      | inl e =>
          change (none : Option Hole) = some h at hb
          cases hb
      | inr b =>
          obtain ⟨e, a⟩ := a
          obtain ⟨f, b⟩ := b
          have same : e = f := by apply Fin.ext; omega
          subst f
          change holeAt ops depth body a = some h at ha
          change holeAt ops depth body b = some h at hb
          exact congrArg (fun x => Sum.inr (Sigma.mk e x)) (unique h a b ha hb)

def boxContext {Op : Type} {ops : Operations Op} {depth bound free : Nat}
    (C : Context ops depth [.term] (List.replicate (bound + free) .term)) :
    Context ops (depth + 1) [.thunk bound] (List.replicate free .term) :=
  ⟨box C.val, box_unique_holes C.val C.property⟩

/-- Shallow plugging works uniformly at every finite hierarchy level. -/
noncomputable def plug {Op : Type} {ops : Operations Op} {depth : Nat} {I O}
    (C : Hypernet ops depth I O) (hole : C.Edge)
    (H : Hypernet ops depth ((alphabet ops depth).signature.input (C.edgeLabel hole))
      ((alphabet ops depth).signature.output (C.edgeLabel hole))) : Hypernet ops depth I O :=
  C.plug hole H

end Hypernets.Linear
