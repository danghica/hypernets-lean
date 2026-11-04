import Hypernets.Copying.PropositionEnvironmentWeakening
import Hypernets.Copying.FullTranslationExamples

/-! Regression instances of the full syntactic theorem. No termination or
purity condition is imposed on a term or on its callbacks. -/
namespace Hypernets.Copying.Weakening.Examples
open Graph BoxPullWeakening
open BoxPullWeakening.RetainedCopy (termResource atomResource)

/-- Every unary and binary operation, including all store operations, is
covered with actual renamed terms in a nonempty mixed environment. -/
def effectTerm (u : Unary) (b : Binary) : Term 2 2 :=
  .binary b (.unary u (.var 1)) (.unary .deref (.atom 1))

noncomputable def all_operations (u : Unary) (b : Binary) (s : ShareSort) :
    Calculation (Translation.castDepth (Translation.depth_rename (effectTerm u b) (termResource s) (atomResource s))
      (Translation.term (Term.rename (termResource s) (atomResource s) (effectTerm u b))))
      (extend (Translation.term (effectTerm u b)) s) := term_weakening _ s

/-- Nested binders keep their own indices while the same outer callback is
used repeatedly and an old atom is read. -/
def repeatedCallback : Term 2 2 :=
  .lam (.lam (Term.seq (.app (.var 2) (.const .unit))
    (Term.seq (.app (.var 2) (.const .unit)) (.unary .deref (.atom 1)))))

noncomputable def nested_repeated_callback (s : ShareSort) :
    Calculation (Translation.castDepth (Translation.depth_rename repeatedCallback (termResource s) (atomResource s))
      (Translation.term (Term.rename (termResource s) (atomResource s) repeatedCallback)))
      (extend (Translation.term repeatedCallback) s) := term_weakening _ s

/-- The usual self-application term is admitted without a termination premise.
This checks weakening for its syntax; it is not a separate divergence proof. -/
noncomputable def self_application (s : ShareSort) :
    Calculation (Translation.castDepth
      (Translation.depth_rename Copying.Examples.omegaTerm (termResource s) (atomResource s))
      (Translation.term (Term.rename (termResource s) (atomResource s) Copying.Examples.omegaTerm)))
      (extend (Translation.term Copying.Examples.omegaTerm) s) := term_weakening _ s

/-- Both unmodified Proposition 12.2 programs in a genuinely mixed environment. -/
noncomputable def proposition_mixed_environment :
    Calculation (Translation.privateCell 2 3) (ambient (Translation.privateCell 0 0) 2 3) ×
    Calculation (Translation.constantResult 2 3) (ambient (Translation.constantResult 0 0) 2 3) :=
  ⟨privateCell_environment 2 3,constantResult_environment 2 3⟩
end Hypernets.Copying.Weakening.Examples
