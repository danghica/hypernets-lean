import Hypernets.Copying.SearchExamples

/-! Exact ordered search on the unchanged Figure 16 binary translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Search
open Graph

/-- This is the original translation, including all zero-resource distributors. -/
def additionGraph := Translation.term (Term.binary (k := 0) (h := 0) .add
  (.const (.nat 1)) (.const (.nat 2)))

def additionHead : additionGraph.Edge := ⟨false,⟨false,(0 : Fin 1)⟩⟩
def additionLeft : additionGraph.Edge := ⟨false,⟨true,⟨false,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩⟩⟩
def additionRight : additionGraph.Edge := ⟨false,⟨true,⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩⟩⟩
def additionArgument (i : Fin 2) : additionGraph.Vertex :=
  additionGraph.targetPort additionHead i

/-- The active head searches its first argument. -/
theorem addition_enter : Step additionGraph (.search,.input 0) (.search,additionArgument 0) := by
  apply Step.search additionHead (.operation (.binary .add)) _ _ rfl
  · change (.input 0 : additionGraph.Vertex) ∈ [.input 0]; exact List.mem_cons_self
  · rfl

/-- The first passive edge returns a value. -/
theorem addition_left : Step additionGraph (.search,additionArgument 0) (.backtrack,additionArgument 0) := by
  apply Step.search additionLeft (.operation (.const (.nat 1))) _ _ rfl
  · change additionArgument 0 ∈ [additionArgument 0]; exact List.mem_cons_self
  · rfl

/-- Returning from argument zero starts argument one, in the paper's order. -/
theorem addition_next : Step additionGraph (.backtrack,additionArgument 0) (.search,additionArgument 1) := by
  exact .backtrack additionHead (.binary .add) (.input 0) _ 0 _ rfl rfl (by decide) rfl rfl

/-- The second passive edge returns a value. -/
theorem addition_right : Step additionGraph (.search,additionArgument 1) (.backtrack,additionArgument 1) := by
  apply Step.search additionRight (.operation (.const (.nat 2))) _ _ rfl
  · change additionArgument 1 ∈ [additionArgument 1]; exact List.mem_cons_self
  · rfl

/-- After both arguments, search hands the unchanged graph to the compute phase. -/
theorem addition_finish : Step additionGraph (.backtrack,additionArgument 1) (.rewrite,.input 0) := by
  exact .backtrack additionHead (.binary .add) (.input 0) _ 1 _ rfl rfl (by decide) rfl rfl

/-- Five search transitions; this deliberately does not assert addition has computed. -/
theorem addition_trace : Trace (Step additionGraph) (.search,.input 0) (.rewrite,.input 0) 5 :=
  .step addition_enter (.step addition_left (.step addition_next (.step addition_right
    (.step addition_finish (.refl _)))))

/-- Any search-only normal run from this initial state has that same cost and endpoint. -/
theorem addition_exact_cost {t n} (run : Trace (Step additionGraph) (.search,.input 0) t n)
    (normal : Terminal (Step additionGraph) t) : n = 5 ∧ t = (.rewrite,.input 0) := by
  have eq := terminal_run_unique run addition_trace normal (fun _ => no_rewrite)
  exact ⟨eq.2,eq.1⟩

/-- The concrete five-step trace survives every larger representation allowance. -/
theorem addition_padded (N : Nat) :
    Trace (Step (Translation.padTo N (Nat.zero_le N) additionGraph))
      ((padTo additionGraph N (Nat.zero_le N)).positions.toFun (.search,.input 0))
      ((padTo additionGraph N (Nat.zero_le N)).positions.toFun (.rewrite,.input 0)) 5 :=
  (padTo_trace_iff additionGraph N (Nat.zero_le N) _ _ 5).mpr addition_trace
end Hypernets.Copying.Search
