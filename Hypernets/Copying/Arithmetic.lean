import Hypernets.Copying.ApplicationExamples

/-! Arithmetic redexes use the unchanged natural-number constants and operations.
Unary minus is zero minus its argument, as clarified by the paper's author. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph

inductive BinaryCode where
  | add | sub
  deriving DecidableEq

def BinaryCode.symbol : BinaryCode → Binary
  | .add => .add
  | .sub => .sub

def BinaryCode.eval : BinaryCode → Nat → Nat → Nat
  | .add, m, n => m+n
  | .sub, m, n => m-n

/-- Natural subtraction is truncated; the clarified unary operation is zero minus n. -/
def neg (n : Nat) : Nat := 0-n

theorem neg_eq_zero (n : Nat) : neg n = 0 := Nat.zero_sub n

def number (d n : Nat) : Hypernet d [.term] [] := primitiveNet d (.operation (.const (.nat n)))
def unaryBefore (d n : Nat) : Hypernet d [.term] [] :=
  Serial.net (primitiveNet d (.operation (.unary .neg))) (number d n)
def unaryAfter (d n : Nat) : Hypernet d [.term] [] := number d (neg n)
def binaryBefore (o : BinaryCode) (d m n : Nat) : Hypernet d [.term] [] :=
  Serial.net (primitiveNet d (.operation (.binary o.symbol))) (Net.Tensor.net (number d m) (number d n))
def binaryAfter (o : BinaryCode) (d m n : Nat) : Hypernet d [.term] [] := number d (o.eval m n)

/-- Only numeric operands occur in these local rules; store and Boolean operations are separate. -/
inductive Rule {d} : Hypernet d [.term] [] → Hypernet d [.term] [] → Prop where
  | unary (n : Nat) : Rule (unaryBefore d n) (unaryAfter d n)
  | binary (o : BinaryCode) (m n : Nat) : Rule (binaryBefore o d m n) (binaryAfter o d m n)

theorem number_raise (d n : Nat) : raise d (number d n) = number (d+1) n := Padding.primitive d _

noncomputable def unaryBefore_raise (d n : Nat) :
    DeepIso (raise d (unaryBefore d n)) (unaryBefore (d+1) n) := by
  simpa only [unaryBefore,Padding.primitive,number_raise] using
    Padding.serial (primitiveNet d (.operation (.unary .neg))) (number d n)

theorem unaryAfter_raise (d n : Nat) : raise d (unaryAfter d n) = unaryAfter (d+1) n := number_raise d _

noncomputable def binaryBefore_raise (o : BinaryCode) (d m n : Nat) :
    DeepIso (raise d (binaryBefore o d m n)) (binaryBefore o (d+1) m n) := by
  simpa only [binaryBefore,Padding.primitive,Padding.tensor,number_raise] using
    Padding.serial (primitiveNet d (.operation (.binary o.symbol))) (Net.Tensor.net (number d m) (number d n))

theorem binaryAfter_raise (o : BinaryCode) (d m n : Nat) :
    raise d (binaryAfter o d m n) = binaryAfter o (d+1) m n := number_raise d _

/-- A numeric result immediately returns through intrinsic search. -/
theorem number_returns (d n : Nat) : Search.Step (number d n) (.search,.input 0) (.backtrack,.input 0) := by
  apply Search.Step.search (G := number d n) (by cases d <;> exact (0 : Fin 1)) (.operation (.const (.nat n))) _ _ (by cases d <;> rfl)
  · cases d <;> exact List.mem_cons_self
  · cases d <;> rfl

/-- The local arithmetic graphs contain no focus or hole labels. -/
theorem safe_number (d n : Nat) : FocusFree (number d n) ∧ HoleFree (number d n) :=
  ⟨(Stable.constant d (.nat n)).focusFree,(Stable.constant d (.nat n)).holeFree⟩

/-- Numeric result corollas retain their labels and incidence under padding. -/
noncomputable def number_raise_iso (d n : Nat) :
    DeepIso (raise d (number d n)) (number (d+1) n) := by
  rw [number_raise]
  exact DeepIso.refl _

end Hypernets.Copying.Arithmetic
