import Hypernets.Copying.DereferenceFrames
import Hypernets.Copying.ContractionTree

/-! Figure 19(b) with arbitrary atom contraction trees and literal term sharing. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

/-- Fill the atom-tree slot, retaining the three primitive interactions. -/
def beforeFill {h} (T : ContractionTree .atom (h+1)) (e : BeforeEdge) :
    Net primitiveSignature (primitiveSignature.input (beforeLabel h e))
      (primitiveSignature.output (beforeLabel h e)) := by
  cases e with
  | reader => exact Net.corolla primitiveSignature (.operation (.unary .deref))
  | inst => exact Net.corolla primitiveSignature .instanceEdge
  | tree => exact T.net
  | store => exact Net.corolla primitiveSignature .store

/-- Fill both slots: preserve the atom tree, and insert precisely D-term-1-2. -/
def afterFill {h} (T : ContractionTree .atom (h+1)) (e : AfterEdge) :
    Net primitiveSignature (primitiveSignature.input (afterLabel h e))
      (primitiveSignature.output (afterLabel h e)) := by
  cases e with
  | discard => exact Net.corolla primitiveSignature (.weakening .term)
  | inst => exact Net.corolla primitiveSignature .instanceEdge
  | tree => exact T.net
  | store => exact Net.corolla primitiveSignature .store
  | share => exact CanonicalTree.net .term 2

/-- The actual dereference redex, with arbitrary additional atom references. -/
def before {h} (T : ContractionTree .atom (h+1)) (d : Nat) : Hypernet d (inputs h) [.term] :=
  ((beforeFrame h).expand (beforeFill T)).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)

/-- The store persists; its content and the result now share through D-term-1-2. -/
def after {h} (T : ContractionTree .atom (h+1)) (d : Nat) : Hypernet d (inputs h) [.term] :=
  ((afterFrame h).expand (afterFill T)).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)

/-- Dereferencing requires a contraction tree, but does not replace the stored value.
Copying must subsequently supply a value through the newly inserted term tree. -/
inductive Rule : {d h : Nat} → Hypernet d (inputs h) [.term] → Hypernet d (inputs h) [.term] → Prop where
  | read {h} (T : ContractionTree .atom (h+1)) (d : Nat) : Rule (before T d) (after T d)

theorem rule_iff {d h} {L R : Hypernet d (inputs h) [.term]} :
    Rule L R ↔ ∃ T : ContractionTree .atom (h+1), L = before T d ∧ R = after T d := by
  constructor
  · intro h; cases h with | read T d => exact ⟨T,rfl,rfl⟩
  · rintro ⟨T,rfl,rfl⟩; exact .read T d

def beforeInstance {h} (T : ContractionTree .atom (h+1)) (d : Nat) : (before T d).Edge := ⟨.inst,(0 : Fin 1)⟩
def afterInstance {h} (T : ContractionTree .atom (h+1)) (d : Nat) : (after T d).Edge := ⟨.inst,(0 : Fin 1)⟩
def beforeStore {h} (T : ContractionTree .atom (h+1)) (d : Nat) : (before T d).Edge := ⟨.store,(0 : Fin 1)⟩
def afterStore {h} (T : ContractionTree .atom (h+1)) (d : Nat) : (after T d).Edge := ⟨.store,(0 : Fin 1)⟩
def beforeTree {h} (T : ContractionTree .atom (h+1)) (d : Nat) (e : T.net.Edge) : (before T d).Edge := ⟨.tree,e⟩
def afterTree {h} (T : ContractionTree .atom (h+1)) (d : Nat) (e : T.net.Edge) : (after T d).Edge := ⟨.tree,e⟩

theorem tree_labels {h} (T : ContractionTree .atom (h+1)) (d : Nat) (e : T.net.Edge) :
    (before T d).edgeLabel (beforeTree T d e) = primitiveLabel d (T.net.edgeLabel e) ∧
    (after T d).edgeLabel (afterTree T d e) = primitiveLabel d (T.net.edgeLabel e) := ⟨rfl,rfl⟩

/-- Raising the allowance does not change either local rule graph. -/
theorem before_raise {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    raise d (before T d) = before T (d+1) := by cases d <;> rfl

theorem after_raise {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    raise d (after T d) = after T (d+1) := by cases d <;> rfl

theorem rule_raise {d h} {L R : Hypernet d (inputs h) [.term]} (s : Rule L R) :
    Rule (raise d L) (raise d R) := by
  obtain ⟨T,rfl,rfl⟩ := rule_iff.mp s
  rw [before_raise,after_raise]; exact .read T (d+1)

/-- The first search step after reading requests copying at the inserted distributor. -/
theorem requests_copy {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Search.Step (after T d) (.search,inputPort h 0) (.rewrite,inputPort h 0) := by
  apply Search.term_contraction (G := after T d) ⟨.share,(2 : Fin 3)⟩ _ rfl
  change inputPort h 0 ∈ [_,inputPort h 0]
  exact List.mem_cons_of_mem _ List.mem_cons_self
end Hypernets.Copying.Dereference
