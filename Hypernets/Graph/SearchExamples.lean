import Hypernets.Graph.Search
import Hypernets.Graph.FocusedExamples

/-! Search-rule checks on concrete corollas, including a skipped thunk. -/
namespace Hypernets.Linear.SearchExamples
open Graph

/-- One operation, with two term arguments followed by a thunk. -/
@[reducible] def ops : Operations Unit := ⟨fun _ => 2, fun _ => [0]⟩

@[reducible] def graph : Hypernet ops 0 [.term] [.term, .term, .thunk 0] :=
  Net.corolla (alphabet ops 0).signature (primitiveLabel ops 0 (.operation ()))

def operation : SearchOperation graph where
  edge := 0
  operation := ()
  label := rfl
  source := .input 0
  arguments := [.output 0, .output 1]
  thunks := [.output 2]
  source_eq := by decide
  target_eq := by decide
  arity := rfl

/-- Entry selects the first argument. -/
theorem enter_first (k : OperationKind) :
    SearchStep graph (fun _ => k) (.search, .input 0) (.search, .output 0) :=
  SearchStep.first_argument operation _ _ rfl

/-- Returning from the first argument selects the second. -/
theorem return_next (k : OperationKind) :
    SearchStep graph (fun _ => k) (.backtrack, .output 0) (.search, .output 1) :=
  SearchStep.next_argument operation 0 _ _ rfl rfl

/-- Returning from the second argument finishes; it does not inspect the thunk. -/
theorem finish_skips_thunk (k : OperationKind) :
    SearchStep graph (fun _ => k) (.backtrack, .output 1) (k.finish, .input 0) :=
  SearchStep.last_argument operation 1 _ rfl rfl

/-- Determinism rules out a mistaken traversal into the thunk target. -/
theorem cannot_search_thunk (k : OperationKind) :
    ¬ SearchStep graph (fun _ => k) (.backtrack, .output 1) (.search, .output 2) := by
  intro bad
  have eq := SearchStep.deterministic (finish_skips_thunk k) bad
  exact k.finish_ne_search (Prod.mk.inj eq).1

/-- The existing nullary value graph finishes by backtracking. -/
theorem value_finishes :
    SearchStep Examples.value (fun _ => .passive) (.search, .input 0) (.backtrack, .input 0) := by
  let a : SearchOperation Examples.value := {
    edge := 0, operation := Examples.Op.value, label := rfl,
    source := .input 0, arguments := [], thunks := [],
    source_eq := by decide, target_eq := by decide, arity := rfl }
  exact SearchStep.nullary a rfl

/-- The variable rule triggers substitution without moving the coordinate. -/
theorem variable_triggers :
    SearchStep Examples.variableFragment (fun _ => .passive)
      (.search, .input 0) (.rewrite, .input 0) :=
  SearchStep.trigger (G := Examples.variableFragment) 0 _ rfl (by decide)

end Hypernets.Linear.SearchExamples
