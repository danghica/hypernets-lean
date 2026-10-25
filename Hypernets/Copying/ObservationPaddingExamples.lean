import Hypernets.Copying.ObservationPadding
import Hypernets.Copying.ContextFillingExamples

/-! A negative semantic regression separates padding invariance from graph
isomorphism invariance. This artificial execution is not the copying UAM. -/
namespace Hypernets.Copying.Examples

/-- A deliberately representation-sensitive execution: no transitions, and
only allowance zero is successful. It ignores every graph label and edge. -/
def depthSensitiveExecution : Execution Nat where
  machine := {
    step := fun _ _ => False
    final := fun d => d = 0
    final_normal := by intros _ _ _ impossible; exact impossible }
  initial := fun P => P.depth

/-- Even determinism does not rule out this dependence on representation depth. -/
theorem depthSensitive_deterministic : depthSensitiveExecution.machine.Deterministic := by
  intro s t u impossible
  exact False.elim impossible

/-- Equal-depth isomorphic graphs are indistinguishable to this execution. -/
theorem depthSensitive_respectsIso : depthSensitiveExecution.RespectsIso := by
  intro d G H gf gh hf hh f
  exact ⟨Machine.Refines.refl _ _,Machine.Refines.refl _ _⟩

/-- The unchanged closed unit translation, with its proved admissibility. -/
def zeroDepthUnit : ClosedProgram :=
  ⟨0,Translation.term (.const .unit : Term 0 0),
    Translation.term_focusFree _,Translation.term_holeFree _⟩

/-- The initializer accepts the unpadded graph as a successful observation. -/
theorem depthSensitive_unit_terminates : depthSensitiveExecution.Terminates zeroDepthUnit :=
  ⟨0,0,Machine.Steps.zero _,rfl⟩

/-- Adding unused allowance changes this artificial observation. -/
theorem depthSensitive_padded_unit_not_terminates :
    ¬ depthSensitiveExecution.Terminates (zeroDepthUnit.pad 1) := by
  rintro ⟨n,s,run,final⟩
  have eq := (run.normal_eq (fun _ impossible => impossible)).2
  change 1 = s at eq
  change s = 0 at final
  omega

/-- Isomorphism invariance alone cannot discharge the padding obligation. -/
theorem depthSensitive_not_respectsPadding : ¬ depthSensitiveExecution.RespectsPadding := by
  intro padding
  have ref := (padding zeroDepthUnit).1
  obtain ⟨n,s,_,run,final⟩ := ref (Machine.Steps.zero _) rfl
  exact depthSensitive_padded_unit_not_terminates ⟨n,s,run,final⟩
end Hypernets.Copying.Examples
