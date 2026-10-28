import Hypernets.Copying.ConverseSpecimenTransfer

/-! Nullary template fragments have no entry ports. This property is structural;
it does not assume anything about execution or contextual equivalence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Every actual pair has the empty input interface. -/
def PreTemplate.NoInputs (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → I = []

/-- Exchanging the two endpoints preserves their empty common interface. -/
theorem PreTemplate.NoInputs.converse {T : PreTemplate} (none : T.NoInputs) :
    T.converse.NoInputs := fun pair => none pair

/-- Nullary fragments in particular have no term inputs. -/
theorem PreTemplate.NoInputs.noTermInputs {T : PreTemplate} (none : T.NoInputs) :
    T.NoTermInputs := by
  intro d I O G H pair i
  have empty := none pair
  subst I
  exact Fin.elim0 i

/-- Output closure follows from the absence of any input-to-output operation path. -/
theorem PreTemplate.NoInputs.outputClosed {T : PreTemplate} (none : T.NoInputs) :
    T.OutputClosed := PreTemplate.NoTermInputs.outputClosed (T := T) none.noTermInputs

/-- The original input-safety predicate is vacuous for nullary fragments,
for every allowed context class and both quantitative parameters. -/
theorem PreTemplate.NoInputs.inputSafe {T : PreTemplate} (none : T.NoInputs)
    (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (Q P : CostOrder) :
    (Specimens.system T Allowed none.outputClosed).InputSafe Q P :=
  Specimens.inputSafe_of_no_term_inputs T none.noTermInputs Allowed none.outputClosed Q P

end Hypernets.Copying
