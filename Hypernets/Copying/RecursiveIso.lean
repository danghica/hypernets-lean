import Hypernets.Graph.RelIso
import Hypernets.Copying.Hierarchy

/-! Recursive isomorphism permits independent carrier renaming inside every box. -/
namespace Hypernets.Copying
open Graph

/-- Related boxes have identical binder metadata and related bodies at that exact interface. -/
inductive BoxRelated (A : Alphabet)
    (R : ∀ {I O}, Net A.signature I O → Net A.signature I O → Prop) : Box A → Box A → Prop where
  | bodies {bound freeVariables freeAtoms} {G H : Net A.signature [.term] (environmentInterface (bound + freeVariables) freeAtoms)}
      (related : R G H) : BoxRelated A R ⟨bound, freeVariables, freeAtoms, G⟩ ⟨bound, freeVariables, freeAtoms, H⟩

/-- Primitive labels agree literally; boxes have equal binding metadata and
recursively isomorphic bodies. Primitive and box labels are never related. -/
def LabelEquiv : (d : Nat) → (alphabet d).Symbol →
    (alphabet d).Symbol → Prop
  | 0, a, b => a = b
  | _ + 1, .inl a, .inl b => a = b
  | d + 1, .inr a, .inr b => BoxRelated (alphabet d)
      (fun G H => Nonempty (Net.RelIso (LabelEquiv d) G H)) a b
  | _ + 1, _, _ => False

/-- An isomorphism of the whole finite hierarchy, preserving ordered boundaries
at every level and permitting unrelated carrier names in corresponding boxes. -/
abbrev DeepIso {d I O} (G H : Hypernet d I O) := Net.RelIso (LabelEquiv d) G H

/-- Recursive label equivalence is reflexive. -/
theorem labelEquiv_refl (d : Nat) (a : (alphabet d).Symbol) :
    LabelEquiv d a a := by
  induction d with
  | zero => rfl
  | succ d ih =>
    cases a with
    | inl a => rfl
    | inr a =>
      cases a with
      | mk bound freeVariables freeAtoms body => exact .bodies ⟨Net.RelIso.refl ih body⟩

/-- Recursive label equivalence is symmetric. -/
theorem labelEquiv_symm (d : Nat) {a b : (alphabet d).Symbol}
    (h : LabelEquiv d a b) : LabelEquiv d b a := by
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
theorem labelEquiv_trans (d : Nat) {a b c : (alphabet d).Symbol}
    (h : LabelEquiv d a b) (k : LabelEquiv d b c) : LabelEquiv d a c := by
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
variable {d I O} {G H K : Hypernet d I O}

def refl (G : Hypernet d I O) : DeepIso G G := Net.RelIso.refl (labelEquiv_refl d) G

def symm (f : DeepIso G H) : DeepIso H G := Net.RelIso.symm (labelEquiv_symm d) f

def trans (f : DeepIso G H) (g : DeepIso H K) : DeepIso G K :=
  Net.RelIso.trans (labelEquiv_trans d) f g

/-- Literal label-preserving isomorphisms embed into recursive isomorphisms. -/
def ofIso (f : Net.Iso G H) : DeepIso G H := Net.RelIso.ofIso (labelEquiv_refl d) f

end DeepIso

/-- Recursively equivalent labels retain their entire ordered input signature. -/
theorem labelEquiv_input (d : Nat) {a b : (alphabet d).Symbol}
    (h : LabelEquiv d a b) :
    (alphabet d).signature.input a = (alphabet d).signature.input b := by
  cases d with
  | zero => exact congrArg _ h
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg (primitiveSignature).input h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => cases h; rfl

/-- Recursively equivalent labels retain their entire ordered output signature. -/
theorem labelEquiv_output (d : Nat) {a b : (alphabet d).Symbol}
    (h : LabelEquiv d a b) :
    (alphabet d).signature.output a = (alphabet d).signature.output b := by
  cases d with
  | zero => exact congrArg _ h
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg (primitiveSignature).output h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => cases h; rfl


end Hypernets.Copying
