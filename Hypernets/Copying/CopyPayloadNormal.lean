import Hypernets.Copying.ApplicationCoherenceExamples

/-! Canonical outer shapes of copyable payloads; recursive box bodies remain unchanged. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening

inductive PlainCode where
  | instanceEdge
  | constant (c : Constant)
  | application
  | unary (o : Unary)
  | binary (o : Binary)
  deriving DecidableEq

def PlainCode.variables : PlainCode → Nat
  | .instanceEdge | .constant _ => 0
  | .application | .binary _ => 2
  | .unary _ => 1

def PlainCode.atoms : PlainCode → Nat
  | .instanceEdge => 1
  | _ => 0

def PlainCode.primitive : PlainCode → Primitive
  | .instanceEdge => .instanceEdge
  | .constant c => .operation (.const c)
  | .application => .operation .app
  | .unary o => .operation (.unary o)
  | .binary o => .operation (.binary o)

def PlainCode.net (c : PlainCode) (d : Nat) : Hypernet d [.term] (environmentInterface c.variables c.atoms) := by
  cases c with
  | instanceEdge => exact primitiveNet d .instanceEdge
  | constant c => exact primitiveNet d (.operation (.const c))
  | application => exact primitiveNet d (.operation .app)
  | unary o => exact primitiveNet d (.operation (.unary o))
  | binary o => exact primitiveNet d (.operation (.binary o))

theorem PlainCode.primitive_injective : Function.Injective PlainCode.primitive := by
  intro a b h; cases a <;> cases b <;> simp_all [primitive]
theorem PlainCode.not_lambda (c : PlainCode) : c.primitive ≠ .operation .lam := by cases c <;> simp [primitive]

def PlainCode.edge (c : PlainCode) (d : Nat) : (c.net d).Edge := by cases d <;> cases c <;> exact (0 : Fin 1)
theorem PlainCode.head (c : PlainCode) (d : Nat) : MatchEmbedding.HeadAt (c.net d) (.input 0) (c.edge d) c.primitive := by
  cases d <;> cases c <;> exact ⟨rfl,List.mem_cons_self⟩
theorem PlainCode.source (c : PlainCode) (d : Nat) : (c.net d).source (c.edge d) = [.input 0] := by cases d <;> cases c <;> rfl
theorem PlainCode.target (c : PlainCode) (d : Nat) : (c.net d).target (c.edge d) = ((List.finRange (environmentInterface c.variables c.atoms).length).map Port.output) := by cases d <;> cases c <;> rfl

inductive NormalForm : {d k h : Nat} → Hypernet d [.term] (environmentInterface k h) → Type 1 where
  | plain (d : Nat) (c : PlainCode) : NormalForm (c.net d)
  | lambda {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) : NormalForm (lambdaPayload B)

theorem normal_form {d k h} {H : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable H) :
    ∃ K, Nonempty (NormalForm K) ∧ Nonempty (DeepIso H K) := by
  induction copyable with
  | instanceEdge d => exact ⟨_,⟨.plain d .instanceEdge⟩,⟨DeepIso.refl _⟩⟩
  | constant d c => exact ⟨_,⟨.plain d (.constant c)⟩,⟨DeepIso.refl _⟩⟩
  | application d => exact ⟨_,⟨.plain d .application⟩,⟨DeepIso.refl _⟩⟩
  | unary d o => exact ⟨_,⟨.plain d (.unary o)⟩,⟨DeepIso.refl _⟩⟩
  | binary d o => exact ⟨_,⟨.plain d (.binary o)⟩,⟨DeepIso.refl _⟩⟩
  | lambda B => exact ⟨_,⟨.lambda B⟩,⟨DeepIso.refl _⟩⟩
  | rename f _ ih => obtain ⟨K,n,⟨g⟩⟩ := ih; exact ⟨K,n,⟨f.symm.trans g⟩⟩

namespace NormalForm
variable {d k h} {H : Hypernet d [.term] (environmentInterface k h)}
def head : (f : NormalForm H) → H.Edge
  | .plain d c => c.edge d
  | .lambda B => Serial.leftEdge _ _ (0 : Fin 1)
def tail : (f : NormalForm H) → H.Edge
  | .plain d c => c.edge d
  | .lambda B => Serial.rightEdge _ _ (0 : Fin 1)
def primitive : NormalForm H → Primitive
  | .plain _ c => c.primitive
  | .lambda _ => .operation .lam

theorem head_at (f : NormalForm H) : MatchEmbedding.HeadAt H (.input 0) f.head f.primitive := by
  cases f with
  | plain d c => exact c.head d
  | lambda B => exact ⟨rfl,List.mem_cons_self⟩
theorem head_source (f : NormalForm H) : H.source f.head = [.input 0] := by
  cases f with
  | plain d c => exact c.source d
  | lambda B => rfl
theorem tail_target (f : NormalForm H) : H.target f.tail = (List.finRange (environmentInterface k h).length).map Port.output := by
  cases f with
  | plain d c => exact c.target d
  | lambda B =>
    change ((Translation.lambdaBox B).target (0 : Fin 1)).map (BoundarySerial.rightInsert _ _) = _
    change ((List.finRange _).map Port.output).map _ = _
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => Application.right_serial_output _ _ i)

theorem copyable (f : NormalForm H) : Copyable H := by
  cases f with
  | plain d c => cases c with
    | instanceEdge => exact .instanceEdge d
    | constant c => exact .constant d c
    | application => exact .application d
    | unary o => exact .unary d o
    | binary o => exact .binary d o
  | lambda B => exact .lambda B
end NormalForm
end Hypernets.Copying.CopyRule
