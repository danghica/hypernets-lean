import Hypernets.Copying.DeepBetaRobustness

/-! A shallow permuted box and an independently certified argument. Stability
makes the argument rigid, and the actual beta successors are recursively isomorphic. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.MixedBeta
open Graph Combined
variable {d k h O} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O}
    (f : BoundaryIso B C) (p : TypedPermutation (environmentInterface k h))

/-- The source has a genuine filling witness, including both independent contributions. -/
noncomputable def sourceWitness (arg : FillingWitness template G H)
    (free : FocusFree B) (action : Opening.Action f p) :
    FillingWitness template (Application.before B G)
      (InterfacePermutation.net (Application.before C H) (p.append (.refl O)).symm) := by
  have payload := (Copying.payloadWitness f p 0 free action).congr (DeepIso.refl _) (Copying.payloadIso p)
  have operands := (payload.tensor arg).congr (DeepIso.refl _)
    (InterfacePermutation.tensor_left (Application.closure C) H p.symm)
  have result := ((FillingWitness.refl (primitiveNet (d+1) (.operation .app))
    (by intro e m eq; cases eq)).serial operands).congr (DeepIso.refl _)
    (InterfacePermutation.serial _ (Net.Tensor.net (Application.closure C) H) (p.symm.append (.refl O)))
  simpa only [primitiveSignature,lambdaPayload,Application.before,Application.closure,TypedPermutation.append_symm,TypedPermutation.symm_refl] using result

noncomputable def successorIso (arg : FillingWitness template G H)
    (stable : Stable G) (action : Opening.Action f p) :
    StateIso ⟨Application.after B G,(.search,.input 0)⟩
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.after C H,(.search,.input 0)⟩) where
  graph := (Opening.afterCompensated f p G action).trans
    (InterfacePermutation.congr (Application.after_congr (DeepIso.refl C) (stable_witness_iso arg stable)) _)
  mode := rfl
  vertex := rfl

/-- The isomorphic residual also supplies an original recursive filling witness. -/
noncomputable def residualWitness (arg : FillingWitness template G H)
    (free : FocusFree B) (stable : Stable G) (action : Opening.Action f p) :
    FillingWitness template (Application.after B G)
      (InterfacePermutation.net (Application.after C H) (p.append (.refl O)).symm) :=
  (FillingWitness.refl _ (Application.after_labels _ B G free stable.focusFree)).congr
    (DeepIso.refl _) (successorIso f p arg stable action).graph

/-- The exact whole-host cost statement, with stability only on the left argument. -/
theorem redex_costs_at (arg : FillingWitness template G H) (stable : Stable G)
    (action : Opening.Action f p) {I J} (K : Hypernet (d+1) I J) (e : K.Edge)
    (hi : [.term] = (alphabet (d+1)).signature.input (K.edgeLabel e))
    (ho : environmentInterface k h ++ O = (alphabet (d+1)).signature.output (K.edgeLabel e))
    (cost : Nat) :
    TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
      ⟨Application.before B G,(.search,.input 0)⟩)) ↔
    TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.before C H,(.search,.input 0)⟩))) :=
  equal_prefix_costs_at K e hi ho
    (Combined.application_run (Application.opening_run B G stable))
    (InterfacePermutation.run _ (Combined.application_run
      (Application.opening_run C H ((arg.stable_iff template_preservesStableLabels).mp stable))))
    (successorIso f p arg stable action) cost
end Hypernets.Copying.BoxPermutation.MixedBeta
