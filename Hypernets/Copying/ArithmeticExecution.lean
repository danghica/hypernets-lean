import Hypernets.Copying.CombinedPaddingExecution

/-! Actual unary and binary arithmetic executions in the combined machine.
Operand order, compute requests, results and exact costs are all explicit. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph

def unaryHead (d n : Nat) : (unaryBefore d n).Edge := by cases d <;> exact ⟨false,(0 : Fin 1)⟩
def unaryValue (d n : Nat) : (unaryBefore d n).Edge := by cases d <;> exact ⟨true,(0 : Fin 1)⟩
def unaryArgument (d n : Nat) : (unaryBefore d n).Vertex := by cases d <;> exact .internal (.inl (0 : Fin 1))

theorem unary_enter (d n : Nat) :
    Search.Step (unaryBefore d n) (.search,.input 0) (.search,unaryArgument d n) := by
  apply Search.Step.search (unaryHead d n) (.operation (.unary .neg)) _ _ (by cases d <;> rfl)
  · cases d <;> exact List.mem_cons_self
  · cases d <;> rfl

theorem unary_value_returns (d n : Nat) :
    Search.Step (unaryBefore d n) (.search,unaryArgument d n) (.backtrack,unaryArgument d n) := by
  apply Search.Step.search (unaryValue d n) (.operation (.const (.nat n))) _ _ (by cases d <;> rfl)
  · cases d <;> exact List.mem_cons_self
  · rfl

theorem unary_ready (d n : Nat) :
    Search.Step (unaryBefore d n) (.backtrack,unaryArgument d n) (.rewrite,.input 0) := by
  apply Search.Step.backtrack (unaryHead d n) (.unary .neg) (.input 0) _ 0 _
    (by cases d <;> rfl) (by cases d <;> rfl) (by simp [Operation.arguments])
  · cases d <;> rfl
  · rfl

def binaryHead (o : BinaryCode) (d m n : Nat) : (binaryBefore o d m n).Edge := by
  cases d <;> exact ⟨false,(0 : Fin 1)⟩
def binaryValue (o : BinaryCode) (d m n : Nat) (b : Bool) : (binaryBefore o d m n).Edge := by
  cases d
  all_goals cases b with
  | false => exact ⟨true,⟨false,(0 : Fin 1)⟩⟩
  | true => exact ⟨true,⟨true,(0 : Fin 1)⟩⟩
def binaryArgument (o : BinaryCode) (d m n : Nat) (i : Fin 2) : (binaryBefore o d m n).Vertex := by
  cases d <;> exact .internal (.inl i)

theorem binary_enter (o : BinaryCode) (d m n : Nat) :
    Search.Step (binaryBefore o d m n) (.search,.input 0) (.search,binaryArgument o d m n 0) := by
  apply Search.Step.search (binaryHead o d m n) (.operation (.binary o.symbol)) _ _ (by cases d <;> rfl)
  · cases d <;> exact List.mem_cons_self
  · cases d <;> rfl

theorem binary_left_returns (o : BinaryCode) (d m n : Nat) :
    Search.Step (binaryBefore o d m n) (.search,binaryArgument o d m n 0) (.backtrack,binaryArgument o d m n 0) := by
  apply Search.Step.search (binaryValue o d m n false) (.operation (.const (.nat m))) _ _ (by cases d <;> rfl)
  · cases d <;> exact List.mem_cons_self
  · rfl

theorem binary_search_right (o : BinaryCode) (d m n : Nat) :
    Search.Step (binaryBefore o d m n) (.backtrack,binaryArgument o d m n 0) (.search,binaryArgument o d m n 1) := by
  apply Search.Step.backtrack (binaryHead o d m n) (.binary o.symbol) (.input 0) _ 0 _
    (by cases d <;> rfl) (by cases d <;> rfl) (by simp [Operation.arguments])
  · cases d <;> rfl
  · cases d <;> rfl

theorem binary_right_returns (o : BinaryCode) (d m n : Nat) :
    Search.Step (binaryBefore o d m n) (.search,binaryArgument o d m n 1) (.backtrack,binaryArgument o d m n 1) := by
  apply Search.Step.search (binaryValue o d m n true) (.operation (.const (.nat n))) _ _ (by cases d <;> rfl)
  · cases d <;> exact List.mem_cons_self
  · rfl

theorem binary_ready (o : BinaryCode) (d m n : Nat) :
    Search.Step (binaryBefore o d m n) (.backtrack,binaryArgument o d m n 1) (.rewrite,.input 0) := by
  apply Search.Step.backtrack (binaryHead o d m n) (.binary o.symbol) (.input 0) _ 1 _
    (by cases d <;> rfl) (by cases d <;> rfl) (by simp [Operation.arguments])
  · cases d <;> rfl
  · rfl

/-- Numeric arithmetic rules are actual combined graph-changing transitions. -/
theorem rule_step {d} {G H : Hypernet d [.term] []} (rule : Rule G H) :
    Combined.Step ⟨G,(.rewrite,.input 0)⟩ ⟨H,(.search,.input 0)⟩ := by
  cases rule with
  | unary n => exact Combined.local_step (.unaryArithmetic d n)
  | binary o m n => exact Combined.local_step (.binaryArithmetic o d m n)

/-- Three search steps, one unary compute step, one numeric return. -/
theorem unary_run (d n : Nat) :
    (Combined.machine d [.term] []).Steps 5 ⟨unaryBefore d n,(.search,.input 0)⟩
      ⟨unaryAfter d n,(.backtrack,.input 0)⟩ :=
  .cons (.search _ (unary_enter d n)) (.cons (.search _ (unary_value_returns d n))
    (.cons (.search _ (unary_ready d n)) (.cons (rule_step (.unary n))
      (.cons (.search _ (number_returns d (neg n))) (.zero _)))))

/-- Ordered evaluation of both operands, one compute step and one return: seven steps. -/
theorem binary_run (o : BinaryCode) (d m n : Nat) :
    (Combined.machine d [.term] []).Steps 7 ⟨binaryBefore o d m n,(.search,.input 0)⟩
      ⟨binaryAfter o d m n,(.backtrack,.input 0)⟩ :=
  .cons (.search _ (binary_enter o d m n)) (.cons (.search _ (binary_left_returns o d m n))
    (.cons (.search _ (binary_search_right o d m n)) (.cons (.search _ (binary_right_returns o d m n))
      (.cons (.search _ (binary_ready o d m n)) (.cons (rule_step (.binary o m n))
        (.cons (.search _ (number_returns d (o.eval m n))) (.zero _)))))))

theorem unary_language (d n : Nat) : Translation.LanguageGraph (unaryBefore d n) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial)
    (Translation.allLabels_primitive _ _ _ trivial)

theorem binary_language (o : BinaryCode) (d m n : Nat) : Translation.LanguageGraph (binaryBefore o d m n) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial)
    (Translation.allLabels_tensor _ (Translation.allLabels_primitive _ _ _ trivial)
      (Translation.allLabels_primitive _ _ _ trivial))

/-- Two operand edges and the binary head are replaced by one numeric-result edge. -/
theorem binary_edge_counts (o : BinaryCode) (d m n : Nat) :
    (binaryBefore o d m n).finiteEdge.elements.length = 3 ∧
      (binaryAfter o d m n).finiteEdge.elements.length = 1 := by cases d <;> exact ⟨rfl,rfl⟩

theorem unary_edge_counts (d n : Nat) :
    (unaryBefore d n).finiteEdge.elements.length = 2 ∧
      (unaryAfter d n).finiteEdge.elements.length = 1 := by cases d <;> exact ⟨rfl,rfl⟩

end Hypernets.Copying.Arithmetic
