import Hypernets.Copying.GeneralContextCongruence

/-! Common-allowance regression for the unchanged programs of Proposition 12.2. -/
namespace Hypernets.Copying.Examples

/-- Both original programs may be supplied to every annotated context at
allowance three. Each result agrees with that context's direct filled-term
translation at a sufficient common allowance, despite depths three and two.
This is structural correspondence, not an assertion that the two programs are
observationally equivalent. -/
theorem proposition12_2_context_representations {v a k h} (C : TermContext v a k h) :
    ContextTranslation.CommonIso
      (ContextTranslation.ofTerm (C.fill (Term.privateCell v a)))
      (ContextTranslation.apply C ⟨3,(translatedProgram (Term.privateCell v a) 3 (by change 3 ≤ 3; decide)).graph⟩) ∧
    ContextTranslation.CommonIso
      (ContextTranslation.ofTerm (C.fill (Term.constantResult v a)))
      (ContextTranslation.apply C ⟨3,(translatedProgram (Term.constantResult v a) 3 (by change 2 ≤ 3; decide)).graph⟩) := by
  constructor
  · have f := ContextTranslation.apply_padTo C (ContextTranslation.ofTerm (Term.privateCell v a)) 3 (by change 3 ≤ 3; decide)
    rwa [ContextTranslation.apply_ofTerm] at f
  · have f := ContextTranslation.apply_padTo C (ContextTranslation.ofTerm (Term.constantResult v a)) 3 (by change 2 ≤ 3; decide)
    rwa [ContextTranslation.apply_ofTerm] at f
end Hypernets.Copying.Examples
