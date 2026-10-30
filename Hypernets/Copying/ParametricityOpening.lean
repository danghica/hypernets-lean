import Hypernets.Copying.ParametricityPadding
import Hypernets.Copying.BoundWeakeningSplice
import Hypernets.Copying.EqualPrefixCosts

/-! The actual original beta steps for Figure 20's smaller abstractions.
Both branches retain the entire unused stable argument under its weakening;
only the live dereference versus literal numeral distinguishes the reducts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined

/-- Opening preserves the literal bound weakening and the private read. -/
theorem open_readBody (d : Nat) : Application.openBody (readBody d) = readBody (d+1) := by
  unfold Application.openBody
  rw [readBody_raise,BoxPullWeakening.cast_eq_reboundary]
  exact Net.reboundary_refl _

/-- Opening preserves the literal bound weakening and numeral 1. -/
theorem open_oneBody (d : Nat) : Application.openBody (oneBody d) = oneBody (d+1) := by
  unfold Application.openBody
  rw [oneBody_raise,BoxPullWeakening.cast_eq_reboundary]
  exact Net.reboundary_refl _

/-- The exact first reduct on the private-read branch, including all original
resource outputs of the unused argument. -/
def readOpened {d O} (V : Hypernet (d+1) [.term] O) :
    Hypernet (d+1) [.term] ([.term] ++ O) :=
  BoundWeakeningSplice.right (primitiveNet (d+1) (.operation (.unary .deref))) V

/-- The exact first reduct on the constant branch. The same discarded
argument remains as a separate component and cannot be erased by beta. -/
def oneOpened {d O} (V : Hypernet (d+1) [.term] O) :
    Hypernet (d+1) [.term] ([] ++ O) :=
  BoundWeakeningSplice.right (primitiveNet (d+1) (.operation (.const (.nat 1)))) V

/-- The factorization is an actual recursive graph isomorphism, not a
semantic argument-discarding rule. -/
def read_openedIso {d O} (V : Hypernet (d+1) [.term] O) :
    DeepIso (Application.after (readBody d) V) (readOpened V) := by
  unfold Application.after
  rw [open_readBody]
  exact BoundWeakeningSplice.iso _ V

def one_openedIso {d O} (V : Hypernet (d+1) [.term] O) :
    DeepIso (Application.after (oneBody d) V) (oneOpened V) := by
  unfold Application.after
  rw [open_oneBody]
  exact BoundWeakeningSplice.iso _ V

/-- The left branch takes precisely the original stable beta rule, with the
same active input before and after the step. -/
theorem read_beta {d O} (V : Hypernet (d+1) [.term] O) (stable : Stable V) :
    Rewrite (Application.before (readBody d) V) (.input 0) (readOpened V) (.input 0) := by
  have step : Rewrite (Application.before (readBody d) V) (.input 0)
      (Application.after (readBody d) V) (.input 0) := .local (.beta _ V stable)
  exact .rename (DeepIso.refl _) (read_openedIso V) step

/-- The right branch likewise performs its actual beta computation. -/
theorem one_beta {d O} (V : Hypernet (d+1) [.term] O) (stable : Stable V) :
    Rewrite (Application.before (oneBody d) V) (.input 0) (oneOpened V) (.input 0) := by
  have step : Rewrite (Application.before (oneBody d) V) (.input 0)
      (Application.after (oneBody d) V) (.input 0) := .local (.beta _ V stable)
  exact .rename (DeepIso.refl _) (one_openedIso V) step

end Hypernets.Copying.Parametricity
