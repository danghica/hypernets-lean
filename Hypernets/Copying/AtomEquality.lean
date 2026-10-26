import Hypernets.Copying.AtomEqualityDifferentFrames

/-! Both Figure 19(d) graph rewrites retain their actual stores and atom trees. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality
open Graph
namespace Same
def beforeFill {h} (T : ContractionTree .atom (h+2)) (e : BeforeEdge) :
    Net primitiveSignature (primitiveSignature.input (beforeLabel h e))
      (primitiveSignature.output (beforeLabel h e)) := by
  cases e with
  | compare => exact Net.corolla primitiveSignature (.operation (.binary .atomEq))
  | left => exact Net.corolla primitiveSignature .instanceEdge
  | right => exact Net.corolla primitiveSignature .instanceEdge
  | tree => exact T.net
  | store => exact Net.corolla primitiveSignature .store
def before {h} (T : ContractionTree .atom (h+2)) (d : Nat) : Hypernet d (inputs h) [.term] :=
  ((beforeFrame h).expand (beforeFill T)).relabel (alphabet d).signature
    (primitiveLabel d) (primitive_input d) (primitive_output d)
def afterFill {h} (T : ContractionTree .atom (h+2)) (e : AfterEdge) :
    Net primitiveSignature (primitiveSignature.input (afterLabel h e))
      (primitiveSignature.output (afterLabel h e)) := by
  cases e with
  | result => exact Net.corolla primitiveSignature (.operation (.const (.bool true)))
  | discardLeft => exact Net.corolla primitiveSignature (.weakening .term)
  | discardRight => exact Net.corolla primitiveSignature (.weakening .term)
  | left => exact Net.corolla primitiveSignature .instanceEdge
  | right => exact Net.corolla primitiveSignature .instanceEdge
  | tree => exact T.net
  | store => exact Net.corolla primitiveSignature .store
def after {h} (T : ContractionTree .atom (h+2)) (d : Nat) : Hypernet d (inputs h) [.term] :=
  ((afterFrame h).expand (afterFill T)).relabel (alphabet d).signature
    (primitiveLabel d) (primitive_input d) (primitive_output d)
inductive Rule : {d h : Nat} → Hypernet d (inputs h) [.term] → Hypernet d (inputs h) [.term] → Prop where
  | compare {h} (T : ContractionTree .atom (h+2)) (d : Nat) : Rule (before T d) (after T d)
def beforeLeft {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (before T d).Edge := ⟨.left,(0 : Fin 1)⟩
def beforeRight {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (before T d).Edge := ⟨.right,(0 : Fin 1)⟩
def beforeStore {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (before T d).Edge := ⟨.store,(0 : Fin 1)⟩
theorem before_raise {h} (T : ContractionTree .atom (h+2)) (d : Nat) : raise d (before T d) = before T (d+1) := by cases d <;> rfl
def afterLeft {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge := ⟨.left,(0 : Fin 1)⟩
def afterRight {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge := ⟨.right,(0 : Fin 1)⟩
def afterStore {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge := ⟨.store,(0 : Fin 1)⟩
theorem after_raise {h} (T : ContractionTree .atom (h+2)) (d : Nat) : raise d (after T d) = after T (d+1) := by cases d <;> rfl
theorem rule_raise {d h} {L R : Hypernet d (inputs h) [.term]} (step : Rule L R) :
    Rule (raise d L) (raise d R) := by
  cases step with
  | compare T d => rw [before_raise,after_raise]; exact .compare T (d+1)
theorem rule_pad {d h} {L R : Hypernet d (inputs h) [.term]} (step : Rule L R) (k : Nat) :
    Rule (Translation.pad d k L) (Translation.pad d k R) := by
  induction k with
  | zero => exact step
  | succ k ih => exact rule_raise ih
end Same
namespace Different
def beforeFill {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (e : BeforeEdge) :
    Net primitiveSignature (primitiveSignature.input (beforeLabel n m e))
      (primitiveSignature.output (beforeLabel n m e)) := by
  cases e with
  | compare => exact Net.corolla primitiveSignature (.operation (.binary .atomEq))
  | left => exact Net.corolla primitiveSignature .instanceEdge
  | right => exact Net.corolla primitiveSignature .instanceEdge
  | tree => exact T.net
  | store => exact Net.corolla primitiveSignature .store
  | treeRight => exact U.net
  | storeRight => exact Net.corolla primitiveSignature .store
def before {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : Hypernet d (inputs n m) [.term,.term] :=
  ((beforeFrame n m).expand (beforeFill T U)).relabel (alphabet d).signature
    (primitiveLabel d) (primitive_input d) (primitive_output d)
def afterFill {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (e : AfterEdge) :
    Net primitiveSignature (primitiveSignature.input (afterLabel n m e))
      (primitiveSignature.output (afterLabel n m e)) := by
  cases e with
  | result => exact Net.corolla primitiveSignature (.operation (.const (.bool false)))
  | discardLeft => exact Net.corolla primitiveSignature (.weakening .term)
  | discardRight => exact Net.corolla primitiveSignature (.weakening .term)
  | left => exact Net.corolla primitiveSignature .instanceEdge
  | right => exact Net.corolla primitiveSignature .instanceEdge
  | tree => exact T.net
  | store => exact Net.corolla primitiveSignature .store
  | treeRight => exact U.net
  | storeRight => exact Net.corolla primitiveSignature .store
def after {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : Hypernet d (inputs n m) [.term,.term] :=
  ((afterFrame n m).expand (afterFill T U)).relabel (alphabet d).signature
    (primitiveLabel d) (primitive_input d) (primitive_output d)
inductive Rule : {d n m : Nat} → Hypernet d (inputs n m) [.term,.term] → Hypernet d (inputs n m) [.term,.term] → Prop where
  | compare {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : Rule (before T U d) (after T U d)
def beforeLeft {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Edge := ⟨.left,(0 : Fin 1)⟩
def beforeRight {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Edge := ⟨.right,(0 : Fin 1)⟩
def beforeStore {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Edge := ⟨.store,(0 : Fin 1)⟩
def beforeStoreRight {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Edge := ⟨.storeRight,(0 : Fin 1)⟩
theorem before_raise {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : raise d (before T U d) = before T U (d+1) := by cases d <;> rfl
def afterLeft {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.left,(0 : Fin 1)⟩
def afterRight {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.right,(0 : Fin 1)⟩
def afterStore {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.store,(0 : Fin 1)⟩
def afterStoreRight {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.storeRight,(0 : Fin 1)⟩
theorem after_raise {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : raise d (after T U d) = after T U (d+1) := by cases d <;> rfl
theorem rule_raise {d n m} {L R : Hypernet d (inputs n m) [.term,.term]} (step : Rule L R) :
    Rule (raise d L) (raise d R) := by
  cases step with
  | compare T U d => rw [before_raise,after_raise]; exact .compare T U (d+1)
theorem rule_pad {d n m} {L R : Hypernet d (inputs n m) [.term,.term]} (step : Rule L R) (k : Nat) :
    Rule (Translation.pad d k L) (Translation.pad d k R) := by
  induction k with
  | zero => exact step
  | succ k ih => exact rule_raise ih
end Different
end Hypernets.Copying.AtomEquality
