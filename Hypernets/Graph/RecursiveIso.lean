import Hypernets.Graph.RelIso
import Hypernets.Graph.DeepInventory

/-! Recursive isomorphism permits independent carrier renaming inside every box. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Related boxes have identical binder metadata and related bodies at that exact interface. -/
inductive BoxRelated (A : Alphabet)
    (R : ∀ {I O}, Net A.signature I O → Net A.signature I O → Prop) : Box A → Box A → Prop where
  | bodies {bound free} {G H : Net A.signature [.term] (List.replicate (bound + free) .term)}
      (related : R G H) : BoxRelated A R ⟨bound, free, G⟩ ⟨bound, free, H⟩

/-- Primitive labels agree literally; boxes have equal binding metadata and
recursively isomorphic bodies. Primitive and box labels are never related. -/
def LabelEquiv (ops : Operations Op) : (d : Nat) → (alphabet ops d).Symbol →
    (alphabet ops d).Symbol → Prop
  | 0, a, b => a = b
  | _ + 1, .inl a, .inl b => a = b
  | d + 1, .inr a, .inr b => BoxRelated (alphabet ops d)
      (fun G H => Nonempty (Net.RelIso (LabelEquiv ops d) G H)) a b
  | _ + 1, _, _ => False

/-- An isomorphism of the whole finite hierarchy, preserving ordered boundaries
at every level and permitting unrelated carrier names in corresponding boxes. -/
abbrev DeepIso {d I O} (G H : Hypernet ops d I O) := Net.RelIso (LabelEquiv ops d) G H

/-- Recursive label equivalence is reflexive. -/
theorem labelEquiv_refl (ops : Operations Op) (d : Nat) (a : (alphabet ops d).Symbol) :
    LabelEquiv ops d a a := by
  induction d with
  | zero => rfl
  | succ d ih =>
    cases a with
    | inl a => rfl
    | inr a =>
      cases a with
      | mk bound free body => exact .bodies ⟨Net.RelIso.refl ih body⟩

/-- Recursive label equivalence is symmetric. -/
theorem labelEquiv_symm (ops : Operations Op) (d : Nat) {a b : (alphabet ops d).Symbol}
    (h : LabelEquiv ops d a b) : LabelEquiv ops d b a := by
  induction d with
  | zero => exact h.symm
  | succ d ih =>
    cases a with
    | inl a => cases b with
      | inl b => exact h.symm
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b =>
        cases h with
        | bodies related =>
          obtain ⟨f⟩ := related
          exact .bodies ⟨Net.RelIso.symm (fun h => ih h) f⟩

/-- Recursive label equivalence is transitive. -/
theorem labelEquiv_trans (ops : Operations Op) (d : Nat) {a b c : (alphabet ops d).Symbol}
    (h : LabelEquiv ops d a b) (k : LabelEquiv ops d b c) : LabelEquiv ops d a c := by
  induction d with
  | zero => exact h.trans k
  | succ d ih =>
    cases a with
    | inl a => cases b with
      | inl b => cases c with
        | inl c => exact h.trans k
        | inr c => exact False.elim k
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => cases c with
        | inl c => exact False.elim k
        | inr c =>
          cases h with
          | bodies related =>
            cases k with
            | bodies related' =>
              obtain ⟨f⟩ := related
              obtain ⟨g⟩ := related'
              exact .bodies ⟨Net.RelIso.trans (fun h k => ih h k) f g⟩

namespace DeepIso
variable {d I O} {G H K : Hypernet ops d I O}

def refl (G : Hypernet ops d I O) : DeepIso G G := Net.RelIso.refl (labelEquiv_refl ops d) G

def symm (f : DeepIso G H) : DeepIso H G := Net.RelIso.symm (labelEquiv_symm ops d) f

def trans (f : DeepIso G H) (g : DeepIso H K) : DeepIso G K :=
  Net.RelIso.trans (labelEquiv_trans ops d) f g

/-- Literal label-preserving isomorphisms embed into recursive isomorphisms. -/
def ofIso (f : Net.Iso G H) : DeepIso G H := Net.RelIso.ofIso (labelEquiv_refl ops d) f

end DeepIso

/-- Recursively equivalent labels retain their entire ordered input signature. -/
theorem labelEquiv_input (ops : Operations Op) (d : Nat) {a b : (alphabet ops d).Symbol}
    (h : LabelEquiv ops d a b) :
    (alphabet ops d).signature.input a = (alphabet ops d).signature.input b := by
  cases d with
  | zero => exact congrArg _ h
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg (primitiveSignature ops).input h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => cases h; rfl

/-- Recursively equivalent labels retain their entire ordered output signature. -/
theorem labelEquiv_output (ops : Operations Op) (d : Nat) {a b : (alphabet ops d).Symbol}
    (h : LabelEquiv ops d a b) :
    (alphabet ops d).signature.output a = (alphabet ops d).signature.output b := by
  cases d with
  | zero => exact congrArg _ h
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg (primitiveSignature ops).output h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => cases h; rfl

/-- Operation labels are preserved and reflected by recursive label equivalence. -/
theorem labelEquiv_isOperation (ops : Operations Op) (d : Nat)
    {a b : (alphabet ops d).Symbol} (h : LabelEquiv ops d a b) :
    IsOperation ops d a ↔ IsOperation ops d b := by
  cases d with
  | zero => cases h; rfl
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => exact Iff.rfl

/-- Transport a complete operation trace, including every endpoint and edge. -/
theorem DeepIso.operationTrace {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H)
    {v w : G.Vertex} {es : List G.Edge}
    (trace : G.OperationTrace (IsOperation ops d) v es w) :
    H.OperationTrace (IsOperation ops d) (Port.map f.vertices.toFun v)
      (es.map f.edges.toFun) (Port.map f.vertices.toFun w) := by
  induction trace with
  | nil v => exact .nil _
  | @cons v w z e es he ht hs tail ih =>
    apply Net.OperationTrace.cons ((labelEquiv_isOperation ops d (f.edge_label e)).mp he)
    · rw [← f.target]; exact List.mem_map_of_mem ht
    · rw [← f.source]; exact List.mem_map_of_mem hs
    · exact ih

/-- Operation traces are preserved and reflected under independent recursive renaming. -/
theorem DeepIso.operationTrace_iff {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H)
    (v w : G.Vertex) (es : List G.Edge) :
    H.OperationTrace (IsOperation ops d) (Port.map f.vertices.toFun v)
      (es.map f.edges.toFun) (Port.map f.vertices.toFun w) ↔
      G.OperationTrace (IsOperation ops d) v es w := by
  constructor
  · intro trace
    have back := DeepIso.operationTrace (DeepIso.symm f) trace
    have inverse (x : G.Vertex) : Port.map f.vertices.invFun (Port.map f.vertices.toFun x) = x :=
      (Port.bijection f.vertices).left_inv x
    simpa [DeepIso.symm, Net.RelIso.symm, Bijection.symm, List.map_map,
      Function.comp_def, f.edges.left_inv, inverse] using back
  · exact DeepIso.operationTrace f

/-- Forward operation paths retain their order and fixed boundary endpoints. -/
theorem DeepIso.operationPath_iff {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H)
    (v w : G.Vertex) (es : List G.Edge) :
    H.OperationPath (IsOperation ops d) (Port.map f.vertices.toFun v)
      (es.map f.edges.toFun) (Port.map f.vertices.toFun w) ↔
      G.OperationPath (IsOperation ops d) v es w := by
  unfold Net.OperationPath
  rw [← List.map_reverse]
  exact DeepIso.operationTrace_iff f w v es.reverse

end Hypernets.Linear
