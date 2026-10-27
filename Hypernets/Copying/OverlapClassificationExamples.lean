import Hypernets.Copying.OperationalTemplates

/-! Concrete nested/mixed overlap and operational-template regressions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.OverlapExamples
open Graph Combined BetaResidualExamples
open ResidualExamples (closedBody closedLeftBody seed)

noncomputable def betaWitness := closedBody.betaBefore argumentWitness
noncomputable def betaMatch :=
  (Application.localMatch closedLeftBody argument).map (Opening.Occurrence.ofIso betaWitness.leftIso.symm)

/-- The complete classifier applies to the mixed nested body, in the original
common context produced by recursive filling assembly. -/
theorem mixed_beta_classified : ApplicationOverlap.Classification (R := betaWitness.right) betaMatch :=
  ApplicationOverlap.classify betaWitness.edges betaMatch

/-- Both original application-frame hops survive the same mixed classification. -/
theorem mixed_beta_path : Trace betaWitness.context.Adjacent betaMatch.app.1 betaMatch.boxEdge.1 2 :=
  ApplicationOverlap.counted_frame_path betaWitness.edges betaMatch

/-- This output is a term output, so beta's one-way proof is not vacuous. The
stable argument is a lambda head with a thunk output available to its context. -/
theorem lambda_term_output_blocked :
    ¬ Search.OperationReachable
      (Application.before (k := 1) (h := 0) (lambdaPayload seed) (primitiveNet 2 (.operation .lam)))
      (.output ⟨0,by decide⟩) :=
  Application.before_oneWay _ _ (Stable.lambda 2) ⟨0,by decide⟩ rfl

/-- The template includes the untouched translation of each numeric argument. -/
theorem reference_pair (n : Nat) :
    (OperationalTemplates.template .referenceCreation).Rel
      (Allocation.before (Allocation.constantArgument n))
      (Allocation.after (Allocation.constantArgument n)) :=
  .witness (DeepIso.refl _) (.reference _ (Allocation.constantArgument_stable n)) (DeepIso.refl _)

/-- The exact operational template also contains the original self-application
body; no claim that its continuation terminates is made. -/
theorem recursive_beta_pair :
    (OperationalTemplates.template .microBeta).Rel
      (Application.before (Translation.term omega) (primitiveNet 2 (.operation (.const .unit))))
      (Application.after (Translation.term omega) (primitiveNet 2 (.operation (.const .unit)))) :=
  .witness (DeepIso.refl _) (.beta (d := 1) (k := 0) (h := 0) _ _
    (Translation.term_focusFree omega) (Stable.constant 2 .unit)) (DeepIso.refl _)

def arithmetic := Arithmetic.binaryBefore .add 5 7 11

def arithmeticWitness : FillingWitness template arithmetic arithmetic :=
  .refl _ (Translation.language_focusFree (Arithmetic.binary_language .add 5 7 11))

/-- The unselected component has genuine independent deep and shallow template
contributions, rather than being assumed identical on both sides. -/
noncomputable def arithmeticHost := FillingWitness.expand BetaResidualExamples.host (BetaResidualExamples.familyWitness arithmeticWitness outsideWitness)

noncomputable def arithmeticMatch : MatchEmbedding arithmetic (arithmeticHost.context.expand arithmeticHost.left) :=
  (MatchEmbedding.expand BetaResidualExamples.host (BetaResidualExamples.family arithmetic outsideLeft) BetaResidualExamples.selected).comp
    (MatchEmbedding.ofDeepIso arithmeticHost.leftIso.symm)

/-- Reconstruct an ordered match of the entire arithmetic redex on the other side. -/
noncomputable def arithmeticAcross : MatchEmbedding arithmetic (arithmeticHost.context.expand arithmeticHost.right) :=
  PrimitiveMatching.across arithmeticHost.context arithmeticHost.edges arithmeticMatch
    (PrimitiveFootprint.binary .add 5 7 11)

/-- Exercise the actual nested expansion rewrite, not a premise that an arbitrary
occurrence is executable. The classifier then constructs its opposite match. -/
theorem arithmetic_rewrite_classified :
    PrimitiveMatchPair (arithmeticHost.context.expand arithmeticHost.left)
      (arithmeticHost.context.expand arithmeticHost.right)
      (arithmeticMatch.ports (.input 0))
      (Net.Expansion.host arithmeticHost.context arithmeticHost.right
        (PrimitiveMatching.down arithmeticHost.context arithmeticHost.edges (arithmeticMatch.ports (.input 0)))) := by
  have step : Rewrite (BetaResidualExamples.host.expand (BetaResidualExamples.family arithmetic outsideLeft))
      (Net.Expansion.insert BetaResidualExamples.host (BetaResidualExamples.family arithmetic outsideLeft) BetaResidualExamples.selected (.input (0 : Fin 1)))
      (BetaResidualExamples.host.expand (BetaResidualExamples.family (Arithmetic.binaryAfter .add 5 7 11) outsideLeft))
      (Net.Expansion.insert BetaResidualExamples.host (BetaResidualExamples.family (Arithmetic.binaryAfter .add 5 7 11) outsideLeft) BetaResidualExamples.selected (.input (0 : Fin 1))) :=
    .expand BetaResidualExamples.host _ _ BetaResidualExamples.selected (BetaResidualExamples.others _ _ _) (.local (.binaryArithmetic .add 5 7 11))
  have renamed := Rewrite.rename arithmeticHost.leftIso.symm (DeepIso.refl _) step
  have head : MatchEmbedding.HeadAt arithmetic (.input 0)
      (⟨false,(0 : Fin 1)⟩ : arithmetic.Edge) (.operation (.binary .add)) := ⟨rfl,List.mem_cons_self⟩
  exact rewrite_basic_case arithmeticHost.context arithmeticHost.edges renamed
    (arithmeticMatch.head head) (by intro eq; cases eq) (by intro eq; cases eq)
end Hypernets.Copying.BoxPermutation.OverlapExamples
