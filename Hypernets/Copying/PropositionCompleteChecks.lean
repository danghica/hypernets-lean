import Hypernets.Copying.PropositionComplete
import Hypernets.Copying.CombinedPaddingInvariant

/-! Semantic regression instances of the completed proposition. These use the
full original context grammar and never assume a callback terminates. -/
namespace Hypernets.Copying.Proposition12_2.CompleteChecks

/-- An arbitrary full-language context preserves the proved example. -/
theorem contextual {v a k h} (C : TermContext v a k h) :
    ObservationalEquiv Combined.execution (C.fill (Term.privateCell v a))
      (C.fill (Term.constantResult v a)) :=
  Combined.observationalEquiv_context C _ _ (Examples.proposition12_2_scoped v a)

/-- The callback's body is the usual self-application loop. -/
def loopingCallback : Term 0 0 :=
  .lam (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0))))

def loopContext : TermContext 0 0 0 0 := .appLeft .hole loopingCallback

/-- The equivalence covers the looping callback without a termination premise.
This theorem compares its observations; it does not assert a separate divergence trace. -/
theorem looping_callback : ObservationalEquiv Combined.execution
    (loopContext.fill (Term.privateCell 0 0)) (loopContext.fill (Term.constantResult 0 0)) :=
  contextual loopContext

/-- Let g be the hole; invoke the same returned closure twice, using unit callbacks. -/
def repeatedContext : TermContext 0 0 0 0 :=
  .appRight (.lam (Term.seq (.app (.var 0) (.lam (.const .unit)))
    (.app (.var 0) (.lam (.const .unit))))) .hole

theorem repeated_closure_use : ObservationalEquiv Combined.execution
    (repeatedContext.fill (Term.privateCell 0 0)) (repeatedContext.fill (Term.constantResult 0 0)) :=
  contextual repeatedContext

/-- Free variables and atoms remain distinct namespaces; the same name can
occur in both lists, exactly as allowed by the public theorem. -/
theorem named_mixed_environment : ObservationalEquiv Combined.execution
    (Term.privateCell (["f","g"] : List String).length (["f","a","b"] : List String).length)
    (Term.constantResult (["f","g"] : List String).length (["f","a","b"] : List String).length) :=
  Examples.proposition12_2 _ _ (by decide) (by decide)

/-- The comparison includes allowances strictly greater than either term needs. -/
theorem extra_allowance : Combined.execution.Equiv CostOrder.any
    (translatedProgram (Term.privateCell 2 3) 7 (by decide))
    (translatedProgram (Term.constantResult 2 3) 7 (by decide)) :=
  Examples.proposition12_2_scoped 2 3 7 (by decide) (by decide)

/-- The original observations quantify over every binding-free graph context. -/
theorem observations {k h N} (left : Translation.depth (Term.privateCell k h) ≤ N)
    (right : Translation.depth (Term.constantResult k h) ≤ N) (C : ClosingContext N k h) :
    Combined.execution.Terminates (C.close (translatedProgram (Term.privateCell k h) N left)) ↔
    Combined.execution.Terminates (C.close (translatedProgram (Term.constantResult k h) N right)) :=
  (Combined.execution.equiv_any_iff _ _).mp (Examples.proposition12_2_scoped k h N left right) C

end Hypernets.Copying.Proposition12_2.CompleteChecks
