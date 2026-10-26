import Hypernets.Copying.ApplicationSafety

/-! Executions with unchanged Figure 16 bodies: unused parameters, delayed
substitution, reference arguments and nested lambda boxes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.Examples
open Graph

/-- One bound variable is present even though the literal does not use it. -/
def constantBody (c : Constant) := Translation.term (Term.const (k := 1) (h := 0) c)
def variableBody := Translation.term (Term.var (k := 1) (h := 0) 0)
def nestedBody := Translation.term (Term.lam (Term.var (k := 2) (h := 0) 0))

theorem constant_body_returns (c : Constant) :
    Search.Step (openBody (constantBody c)) (.search,.input 0) (.backtrack,.input 0) := by
  apply Search.Step.search (G := openBody (constantBody c)) ⟨false,⟨true,(0 : Fin 1)⟩⟩ (.operation (.const c)) _ _ rfl
  · change (.input 0 : (openBody (constantBody c)).Vertex) ∈ [.input 0]; exact List.mem_cons_self
  · rfl

/-- The original D_{1,1} survives beta: using the parameter next requests copying. -/
theorem variable_body_requests_copy :
    Search.Step (openBody variableBody) (.search,.input 0) (.rewrite,.input 0) := by
  apply Search.term_contraction (G := openBody variableBody) ⟨false,⟨false,⟨true,⟨0,1⟩⟩⟩⟩ _ rfl
  change (.input 0 : (openBody variableBody).Vertex) ∈ [_,.input 0]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Opening an outer lambda does not open the nested lambda's box. -/
theorem nested_body_returns :
    Search.Step (openBody nestedBody) (.search,.input 0) (.backtrack,.input 0) := by
  apply Search.Step.search (G := openBody nestedBody) ⟨false,⟨false,(0 : Fin 1)⟩⟩ (.operation .lam) _ _ rfl
  · change (.input 0 : (openBody nestedBody).Vertex) ∈ [.input 0]; exact List.mem_cons_self
  · rfl

theorem constant_after_returns {O} (c : Constant) (G : Hypernet 1 [.term] O) :
    Search.Step (after (constantBody c) G) (.search,.input 0) (.backtrack,.input 0) := by
  simpa only [after,body_input] using body_search (openBody (constantBody c)) G (constant_body_returns c)

theorem variable_after_requests_copy {O} (G : Hypernet 1 [.term] O) :
    Search.Step (after variableBody G) (.search,.input 0) (.rewrite,.input 0) := by
  simpa only [after,body_input] using body_search (openBody variableBody) G variable_body_requests_copy

theorem nested_after_returns {O} (G : Hypernet 2 [.term] O) :
    Search.Step (after nestedBody G) (.search,.input 0) (.backtrack,.input 0) := by
  simpa only [after,body_input] using body_search (openBody nestedBody) G nested_body_returns

/-- Seven transitions return a constant, still requiring the unused argument to be stable. -/
theorem constant_run {O} (c : Constant) (G : Hypernet 1 [.term] O) (stable : Stable G) :
    (machine 1 ([] ++ O)).Steps 7 ⟨before (constantBody c) G,(.search,.input 0)⟩
      ⟨after (constantBody c) G,(.backtrack,.input 0)⟩ := by
  exact (opening_run (constantBody c) G stable).append
    (.cons (.search _ (constant_after_returns c G)) (.zero _))

/-- This endpoint is a copy request, not a substituted value or an asserted termination. -/
theorem variable_run {O} (G : Hypernet 1 [.term] O) (stable : Stable G) :
    (machine 1 ([] ++ O)).Steps 7 ⟨before variableBody G,(.search,.input 0)⟩
      ⟨after variableBody G,(.rewrite,.input 0)⟩ := by
  exact (opening_run variableBody G stable).append
    (.cons (.search _ (variable_after_requests_copy G)) (.zero _))

theorem nested_run {O} (G : Hypernet 2 [.term] O) (stable : Stable G) :
    (machine 2 ([] ++ O)).Steps 7 ⟨before nestedBody G,(.search,.input 0)⟩
      ⟨after nestedBody G,(.backtrack,.input 0)⟩ := by
  exact (opening_run nestedBody G stable).append
    (.cons (.search _ (nested_after_returns G)) (.zero _))

/-- A reference argument retains its atom attachment after an unused-argument call. -/
theorem reference_argument_run :
    (machine 1 [.atom]).Steps 7
      ⟨before (constantBody (.nat 1)) (primitiveNet 1 .instanceEdge),(.search,.input 0)⟩
      ⟨after (constantBody (.nat 1)) (primitiveNet 1 .instanceEdge),(.backtrack,.input 0)⟩ :=
  constant_run _ _ (Stable.instanceEdge 1)

theorem unused_argument_still_must_be_stable :
    ¬ Stable (primitiveNet 1 (.operation .app)) := active_not_stable 1 .app rfl
end Hypernets.Copying.Application.Examples
