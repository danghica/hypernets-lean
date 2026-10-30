import Hypernets.Copying.ParametricityLargeSplice
import Hypernets.Copying.ApplicationTransport

/-! Literal one-step opening of the larger Figure20 abstractions. The entire
callback f() stays an unevaluated graph and retains the original D1,1. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LargeOpening
open Graph Combined
variable {d : Nat} {O : List Wire} (V : Hypernet (d+2) [.term] O)

/-- The original callback connected to its evaluated f argument, with no
transition of the callback included in this definition. -/
def invocation : Hypernet (d+2) [.term] O := Serial.net (callback (d+2)) V

def readOpened : Hypernet (d+2) [.term] ([.term] ++ O) :=
  LargeSplice.target (hasPrivate := true) (smallLeft (d+1)) (callback (d+2)) V

def oneOpened : Hypernet (d+2) [.term] ([] ++ O) :=
  LargeSplice.target (hasPrivate := false) (smallRight (d+1)) (callback (d+2)) V

/-- The opened left body is the actual raised original displayed call/read
body, with its selected bound output still first. -/
noncomputable def read_bodyIso : DeepIso (Application.openBody (callReadBody d))
    (LargeSplice.body (hasPrivate := true) (smallLeft (d+1)) (callback (d+2))) := by
  simpa only [Application.openBody,BoxPullWeakening.cast_eq_reboundary,Net.reboundary_refl,
    LargeSplice.body,LargeSplice.raw,LargeSplice.freeInterface,callReadBody,callOneBody,environmentInterface]
    using callReadBody_raise d

/-- The right body has the same unevaluated callback and the original smaller
constant-returning abstraction. -/
noncomputable def one_bodyIso : DeepIso (Application.openBody (callOneBody d))
    (LargeSplice.body (hasPrivate := false) (smallRight (d+1)) (callback (d+2))) := by
  simpa only [Application.openBody,BoxPullWeakening.cast_eq_reboundary,Net.reboundary_refl,
    LargeSplice.body,LargeSplice.raw,LargeSplice.freeInterface,callReadBody,callOneBody,environmentInterface]
    using callOneBody_raise d

/-- The factorization is a full original graph isomorphism, independent of
all callback behavior and of stability of V. -/
noncomputable def read_openedIso : DeepIso (Application.after (callReadBody d) V) (readOpened V) :=
  (Application.splice_congr (read_bodyIso (d := d)) (DeepIso.refl V)).trans
    (LargeSplice.iso (hasPrivate := true) (smallLeft (d+1)) (callback (d+2)) V).symm

noncomputable def one_openedIso : DeepIso (Application.after (callOneBody d) V) (oneOpened V) :=
  (Application.splice_congr (one_bodyIso (d := d)) (DeepIso.refl V)).trans
    (LargeSplice.iso (hasPrivate := false) (smallRight (d+1)) (callback (d+2)) V).symm

/-- The larger private-read abstraction takes exactly one actual original
beta step and retains an application of the smaller abstraction to f(). -/
theorem read_beta (stable : Stable V) :
    Rewrite (Application.before (callReadBody d) V) (.input 0) (readOpened V) (.input 0) :=
  (Rewrite.local (.beta (callReadBody d) V stable)).rename (DeepIso.refl _) (read_openedIso V)

/-- The corresponding constant abstraction takes the same single beta step;
no callback evaluation or successful-termination premise is introduced. -/
theorem one_beta (stable : Stable V) :
    Rewrite (Application.before (callOneBody d) V) (.input 0) (oneOpened V) (.input 0) :=
  (Rewrite.local (.beta (callOneBody d) V stable)).rename (DeepIso.refl _) (one_openedIso V)
end Hypernets.Copying.Parametricity.LargeOpening
