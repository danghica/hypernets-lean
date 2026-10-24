import Hypernets.Graph.SearchQuotientExecutions
import Hypernets.Graph.QuotientSearchExamples
import Hypernets.Graph.RecursiveIsoExamples

/-! Recursive box renaming and exact-length search execution regressions. -/
namespace Hypernets.Linear.Examples
open Graph

/-- The concrete two-hole box contains no focus, including in its body. -/
theorem boxedTwoHoles_focusFree : FocusFree boxedTwoHoles := by
  intro e
  exact twoHoles_focusFree

/-- A nontrivial body renaming preserves global focus freedom even though the
boxed graphs admit no literal-label isomorphism. -/
theorem renamedBoxedTwoHoles_focusFree : FocusFree renamedBoxedTwoHoles :=
  (DeepIso.focusFree_iff boxedTwoHoles_deepIso).mp boxedTwoHoles_focusFree

/-- The concrete value executes in exactly one step on the recursive quotient. -/
theorem value_deep_run :
    (DeepStateClass.searchMachine (fun _ => .passive)).Steps 1
      (DeepStateClass.ofState initialValue) (DeepStateClass.ofState finalValue) :=
  .cons (t := DeepStateClass.ofState finalValue) (State.search_deepSearch value_search_final) (.zero _)

/-- Exact-length lifting recovers a successful one-step run from the reconstructed
literal source class, not only from the original named state. -/
theorem recovered_value_lift :
    ∃ u, (StateClass.searchMachine (fun _ => .passive)).Steps 1
      (StateClass.ofState recoveredValue) u ∧ StateClass.Final u := by
  apply (StateClass.final_run_toDeep_iff 1 (StateClass.ofState recoveredValue)).mp
  refine ⟨DeepStateClass.ofState finalValue, ?_, value_boundary_states.2⟩
  rw [recovered_value_class]
  exact value_deep_run

/-- Search completion remains a normal form after forgetting all body names. -/
theorem final_value_deep_normal :
    ¬ ∃ t, DeepStateClass.Search (fun _ => .passive) (DeepStateClass.ofState finalValue) t := by
  rintro ⟨t, step⟩
  exact DeepStateClass.final_no_search (s := DeepStateClass.ofState finalValue) value_boundary_states.2 step

end Hypernets.Linear.Examples
