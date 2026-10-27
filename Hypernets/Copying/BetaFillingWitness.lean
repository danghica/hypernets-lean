import Hypernets.Copying.StableFillingRigidity

/-! Actual recursive certificates before and after micro-beta, using the
original bound-output splice and its one-step depth increase. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

/-- Connect exactly bound output zero, leaving the free and argument output blocks intact. -/
def splice {d F O} {B C : Hypernet d [.term] (.term :: F)} {G H : Hypernet d [.term] O}
    (body : FillingWitness T B C) (arg : FillingWitness T G H) :
    FillingWitness T (Application.splice B G) (Application.splice C H) := by
  apply expand (Application.splicePattern d F O)
  intro b
  cases d <;> cases b
  all_goals first | exact body | exact arg

def betaBefore {d k h O} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O} (body : FillingWitness T B C) (arg : FillingWitness T G H) :
    FillingWitness T (Application.before B G) (Application.before C H) :=
  (refl (primitiveNet (d+1) (.operation .app)) (by intro e m eq; cases eq)).serial
    (body.lambdaPayload.tensor arg)

noncomputable def openBody (closed : T.PaddingClosed) {d k h}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)} (body : FillingWitness T B C) :
    FillingWitness T (Application.openBody B) (Application.openBody C) :=
  (body.raise closed).interfaces rfl (BoxPermutation.Opening.interface k h)

/-- Unlike the shallow beta overlap, the exposed bodies can remain genuinely
related by nested template occurrences after the outer boxes disappear. -/
noncomputable def betaAfter (closed : T.PaddingClosed) {d k h O}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O} (body : FillingWitness T B C) (arg : FillingWitness T G H) :
    FillingWitness T (Application.after B G) (Application.after C H) :=
  (body.openBody closed).splice arg
end Hypernets.Copying.FillingWitness

namespace Hypernets.Copying.BoxPermutation.DeepBeta
open Graph Combined
variable {d k h O} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O}

/-- The second stability premise is derived from the paired argument certificate. -/
theorem diamond (body : FillingWitness template B C) (arg : FillingWitness template G H)
    (stable : Stable G) :
    Combined.Step ⟨Application.before B G,(.rewrite,.input 0)⟩
      ⟨Application.after B G,(.search,.input 0)⟩ ∧
    Combined.Step ⟨Application.before C H,(.rewrite,.input 0)⟩
      ⟨Application.after C H,(.search,.input 0)⟩ ∧
    Nonempty (FillingWitness template (Application.after B G) (Application.after C H)) :=
  ⟨Combined.local_step (.beta B G stable),
    Combined.local_step (.beta C H ((arg.stable_iff template_preservesStableLabels).mp stable)),
    ⟨body.betaAfter template_paddingClosed arg⟩⟩

/-- Both original search-plus-compute prefixes still have length six. -/
theorem opening (body : FillingWitness template B C) (arg : FillingWitness template G H)
    (stable : Stable G) :
    (Combined.machine (d+1) [.term] (environmentInterface k h ++ O)).Steps 6
      ⟨Application.before B G,(.search,.input 0)⟩ ⟨Application.after B G,(.search,.input 0)⟩ ∧
    (Combined.machine (d+1) [.term] (environmentInterface k h ++ O)).Steps 6
      ⟨Application.before C H,(.search,.input 0)⟩ ⟨Application.after C H,(.search,.input 0)⟩ ∧
    Nonempty (FillingWitness template (Application.after B G) (Application.after C H)) :=
  ⟨Combined.application_run (Application.opening_run B G stable),
    Combined.application_run (Application.opening_run C H ((arg.stable_iff template_preservesStableLabels).mp stable)),
    ⟨body.betaAfter template_paddingClosed arg⟩⟩
end Hypernets.Copying.BoxPermutation.DeepBeta
