import Hypernets.Copying.TranslatedSpecimens
import Hypernets.Copying.SpecimenExamples

/-! Regressions for the observation bridge; none assert unproved template robustness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContextualRobustnessExamples
open Graph Combined

/-- Arbitrary numeral pairs have genuine initial lifting witnesses in every
original closing context, without claiming equivalence of the numerals. -/
theorem numbers_initial (d n m : Nat) (C : ClosingContext d 0 0) :
    let G : OpenProgram d 0 0 := ⟨Arithmetic.number d n,(Arithmetic.safe_number d n).1,(Arithmetic.safe_number d n).2⟩
    let H : OpenProgram d 0 0 := ⟨Arithmetic.number d m,(Arithmetic.safe_number d m).1,(Arithmetic.safe_number d m).2⟩
    (Specimens.system SpecimenExamples.numbers Specimens.bindingFreeContexts SpecimenExamples.numbers_closed).Lifting
      (StateClass.execution.initial (C.close G)) (StateClass.execution.initial (C.close H)) :=
  Specimens.closing_initial_lifting _ _ C _ _ (.pair d n m)

/-- This deliberately broad relation checks structural certificates only. -/
def focusFreePairs : PreTemplate where
  Rel G H := FocusFree G ∧ FocusFree H
  focus_free pair := pair

/-- Structural filling does not establish the semantic template hypotheses. -/
theorem focusFreePairs_not_closed : ¬ focusFreePairs.OutputClosed := by
  intro closed
  have free : FocusFree (primitiveNet 0 (.operation (.unary .neg))) := by intro e m eq; cases eq
  rcases closed (G := primitiveNet 0 (.operation (.unary .neg))) ⟨free,free⟩ with one | one
  · exact SpecimenExamples.negation_not_oneWay one
  · exact SpecimenExamples.negation_not_oneWay one

/-- A real translated hole beneath two lambda binders, with both bound variables
in its interface. The two fillings select different binders; the certificate
retains each actual translation and never identifies the results. -/
theorem nested_binders :
    let C : TermContext 2 0 0 0 := .lam (.lam .hole)
    ∃ n, ∃ D : ClosingContext n 2 0, ∃ L R,
      DeepFilling focusFreePairs D.graph L R ∧
      ContextTranslation.ScopedIso (k := 0) (h := 0) ⟨D.depth,L⟩
        (ContextTranslation.ofTerm (C.fill (.var 0))) ∧
      ContextTranslation.ScopedIso (k := 0) (h := 0) ⟨D.depth,R⟩
        (ContextTranslation.ofTerm (C.fill (.var 1))) := by
  let C : TermContext 2 0 0 0 := .lam (.lam .hole)
  obtain ⟨n,D,_,_,law⟩ := ContextTranslation.closing_context C 0 7
  let G := (translatedProgram (Term.var 0 : Term 2 0) 0 (by decide)).pad n
  let H := (translatedProgram (Term.var 1 : Term 2 0) 0 (by decide)).pad n
  obtain ⟨L,R,pair,_,_,⟨li⟩,⟨ri⟩⟩ := AddressedFillings.closing focusFreePairs D G H ⟨G.focusFree,H.focusFree⟩
  have left := law (Translation.term (Term.var 0 : Term 2 0))
  have right := law (Translation.term (Term.var 1 : Term 2 0))
  change ContextTranslation.ScopedIso _ (ContextTranslation.apply C (ContextTranslation.ofTerm (Term.var 0 : Term 2 0))) at left
  change ContextTranslation.ScopedIso _ (ContextTranslation.apply C (ContextTranslation.ofTerm (Term.var 1 : Term 2 0))) at right
  rw [ContextTranslation.apply_ofTerm] at left right
  refine ⟨0+n,D,L,R,pair,?_,?_⟩
  · exact (ContextTranslation.ScopedIso.ofIso (k := 0) (h := 0) li).trans left
  · exact (ContextTranslation.ScopedIso.ofIso (k := 0) (h := 0) ri).trans right

/-- The bridge's contexts still exclude the checked zero-input closure failure. -/
theorem sourced_hole_required {d k h} (C : ClosingContext d k h) :
    BindingFree.SourcedHole C.site :=
  SoleHole.sourced C.site C.sole (by decide)
end Hypernets.Copying.ContextualRobustnessExamples
