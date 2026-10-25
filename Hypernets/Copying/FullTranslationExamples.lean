import Hypernets.Copying.Translation

namespace Hypernets.Copying.Examples
open Graph

/-- Figure 16's exchange sends x0,x1,a0,x0,x1,a0 to x0,x1,x0,x1,a0,a0. -/
theorem binary_environment_permutation :
    let p := InterfaceShuffle.bijection [Wire.term,Wire.term] [Wire.atom]
      [Wire.term,Wire.term] [Wire.atom]
    (p.toFun ⟨0,by decide⟩).val = 0 ∧ (p.toFun ⟨1,by decide⟩).val = 1 ∧ (p.toFun ⟨2,by decide⟩).val = 4 ∧
    (p.toFun ⟨3,by decide⟩).val = 2 ∧ (p.toFun ⟨4,by decide⟩).val = 3 ∧ (p.toFun ⟨5,by decide⟩).val = 5 := by decide

/-- Application retains both constant graphs and three two-use canonical trees. -/
theorem application_environment_edges :
    (Translation.application (Translation.constant 0 2 1 .unit)
      (Translation.constant 0 2 1 (.nat 1))).finiteEdge.elements.length = 18 := by decide

/-- The same wiring is present for arithmetic, assignment, and atom equality. -/
theorem binary_environment_edges (o : Binary) :
    (Translation.binary o (Translation.constant 0 2 1 .unit)
      (Translation.constant 0 2 1 (.nat 1))).finiteEdge.elements.length = 18 := by
  cases o <;> decide

/-- The original left program has three nested abstraction levels, including let/sequence sugar. -/
theorem privateCell_depth (k h : Nat) : Translation.depth (Term.privateCell k h) = 3 := rfl

theorem constantResult_depth (k h : Nat) : Translation.depth (Term.constantResult k h) = 2 := rfl

/-- Closed left translation retains the outer application, lambda/box, ref, and numeral. -/
theorem privateCell_outer_edges :
    (Translation.privateCell 0 0).finiteEdge.elements.length = 5 := by decide

/-- The closed right translation has lambda and box outside its translated body. -/
theorem constantResult_outer_edges :
    (Translation.constantResult 0 0).finiteEdge.elements.length = 2 := by decide

/-- Both actual translated programs satisfy global graph-language invariants in every named environment. -/
theorem proposition12_2_graphs_wellFormed {Name : Type} (E : Environment Name) :
    FocusFree (Translation.privateCell E.variables.length E.atoms.length) ∧
    HoleFree (Translation.privateCell E.variables.length E.atoms.length) ∧
    FocusFree (Translation.constantResult E.variables.length E.atoms.length) ∧
    HoleFree (Translation.constantResult E.variables.length E.atoms.length) :=
  ⟨Translation.term_focusFree _,Translation.term_holeFree _,
    Translation.term_focusFree _,Translation.term_holeFree _⟩

/-- Structural regression for self-application; no termination assertion is made. -/
def omegaTerm : Term 0 0 :=
  .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

theorem omega_translation_language : Translation.LanguageGraph (Translation.term omegaTerm) :=
  Translation.term_language _

/-- Different subterm box depths are handled without adding outer graph edges. -/
theorem unequal_depth_application_edges :
    (Translation.term (Term.app (Term.lam (Term.var 0)) (Term.const .unit) : Term 0 0)).finiteEdge.elements.length = 4 := by decide

end Hypernets.Copying.Examples
