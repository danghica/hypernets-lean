import Hypernets.Copying.BPermExactExecution

/-! Whole-graph regressions with a non-boundary active token and an independently
changed surrounding component. These exercise the universal transport theorem. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.FullExamples
open Graph Combined BetaResidualExamples ResidualExamples

/-- A basic operation transports while a disjoint component contains separately
certified nested and shallow BPerm occurrences. The residual is constructed. -/
theorem arithmetic_mixed_host :
    ∃ H w, Rewrite (BetaResidualExamples.host.expand
        (BetaResidualExamples.family OverlapExamples.arithmetic outsideRight))
      (Net.Expansion.insert BetaResidualExamples.host
        (BetaResidualExamples.family OverlapExamples.arithmetic outsideRight) BetaResidualExamples.selected (.input (0 : Fin 1))) H w ∧
      Nonempty (PointedFilling (BetaResidualExamples.host.expand
        (BetaResidualExamples.family (Arithmetic.binaryAfter .add 5 7 11) outsideLeft))
        (Net.Expansion.insert BetaResidualExamples.host
          (BetaResidualExamples.family (Arithmetic.binaryAfter .add 5 7 11) outsideLeft)
          BetaResidualExamples.selected (.input (0 : Fin 1))) H w) := by
  let p := PointedFilling.expandAt BetaResidualExamples.host
    (BetaResidualExamples.familyWitness OverlapExamples.arithmeticWitness outsideWitness)
    BetaResidualExamples.selected (.input (0 : Fin 1))
  exact p.rewrite (.expand BetaResidualExamples.host _ _ BetaResidualExamples.selected
    (BetaResidualExamples.others _ _ _) (.local (.binaryArithmetic .add 5 7 11)))

/-- Deep beta opening works in the same mixed host, at the actual internal
resume coordinate and without assuming that the surrounding component agrees. -/
theorem beta_mixed_host :
    ∃ H w, Rewrite (BetaResidualExamples.host.expand
        (BetaResidualExamples.family (Application.before closedRightBody argument) outsideRight))
      (Net.Expansion.insert BetaResidualExamples.host
        (BetaResidualExamples.family (Application.before closedRightBody argument) outsideRight)
        BetaResidualExamples.selected (.input (0 : Fin 1))) H w ∧
      Nonempty (PointedFilling (BetaResidualExamples.host.expand
        (BetaResidualExamples.family (Application.after closedLeftBody argument) outsideLeft))
        (Net.Expansion.insert BetaResidualExamples.host
          (BetaResidualExamples.family (Application.after closedLeftBody argument) outsideLeft)
          BetaResidualExamples.selected (.input (0 : Fin 1))) H w) := by
  let p := PointedFilling.expandAt BetaResidualExamples.host
    (BetaResidualExamples.familyWitness OverlapExamples.betaWitness outsideWitness)
    BetaResidualExamples.selected (.input (0 : Fin 1))
  exact p.rewrite (.expand BetaResidualExamples.host _ _ BetaResidualExamples.selected
    (BetaResidualExamples.others _ _ _) (.local (.beta closedLeftBody argument (Stable.constant 5 .unit))))

/-- The regression really uses an internal context position. -/
theorem host_token_not_input :
    ¬ (BetaResidualExamples.host.sourcePort BetaResidualExamples.selected (0 : Fin 1)).IsInput :=
  BetaResidualExamples.token_internal
end Hypernets.Copying.BoxPermutation.FullExamples
