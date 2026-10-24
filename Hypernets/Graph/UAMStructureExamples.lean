import Hypernets.Graph.UAMStructure
import Hypernets.Graph.UAMExamples

/-! Non-vacuous regressions for the full-UAM structural theorem. -/
namespace Hypernets.Linear.UAMStructureExamples
open Graph

/-- Search actually reaches the variable-removal source from its initial graph. -/
theorem source_rooted : State.Rooted (fun _ => .passive) UAMExamples.source := by
  let G := Substitution.prefixVariable Examples.value
  let p : TypedPosition G := ⟨(.rewrite,.input 0),rfl⟩
  have run : (coordinateMachine G (fun _ => .passive)).Steps 1 (.search,.input 0) p.val :=
    .cons (SearchStep.trigger (G := G) (.inr 0) (.input 0) rfl rfl) (.zero _)
  exact p.realize_rooted (Substitution.variable_free _ Examples.value_focusFree)
    (Substitution.variable_closed _ Examples.value_holeFree) run

/-- The concrete substitution theorem applies to that rooted execution. -/
theorem substitution_rooted : State.Rooted (fun _ => .passive) Examples.initialValue :=
  State.substitution_rooted UAMExamples.substitute source_rooted

/-- Every alternative decomposition of this source yields the same reduct class. -/
theorem substitution_unique {t : State Examples.operations 0}
    (step : State.Substitution UAMExamples.source t) :
    Nonempty (Focussed.DeepIso t.focussed Examples.initialValue.focussed) :=
  State.substitution_deterministic step UAMExamples.substitute

/-- The revisit theorem produces a genuinely nonempty suffix in the actual machine. -/
theorem source_revisit : ∃ a b, 0 < b ∧
    (DeepStateClass.searchMachine (fun _ => .passive)).Steps a
      (DeepStateClass.root (DeepStateClass.ofState UAMExamples.source))
      (DeepStateClass.restart (DeepStateClass.ofState UAMExamples.source)) ∧
    (DeepStateClass.searchMachine (fun _ => .passive)).Steps b
      (DeepStateClass.restart (DeepStateClass.ofState UAMExamples.source))
      (DeepStateClass.ofState UAMExamples.source) :=
  State.rooted_revisit source_rooted (by intro h; cases h)

/-- The existing singleton extrinsic behaviour is deterministic. -/
theorem behaviour_deterministic : DeterministicModulo UAMExamples.behaviour.step := by
  rintro s t u ⟨_,rfl⟩ ⟨_,rfl⟩
  exact ⟨Focussed.DeepIso.refl _⟩

/-- Its actual target is initial, so it also preserves rootedness. -/
theorem behaviour_refocusing : RefocusingStates (fun _ => .active) UAMExamples.behaviour.step := by
  rintro s t _ ⟨_,rfl⟩
  exact DeepStateClass.initial_rooted ⟨rfl,trivial⟩

/-- The structural theorem covers a machine with a genuine compute transition. -/
theorem full_structural : DeterministicModulo (UAM.Step UAMExamples.behaviour) ∧
    RefocusingStates (fun _ => .active) (UAM.Step UAMExamples.behaviour) :=
  ⟨UAM.deterministic _ behaviour_deterministic,UAM.refocusing _ behaviour_refocusing⟩
end Hypernets.Linear.UAMStructureExamples
