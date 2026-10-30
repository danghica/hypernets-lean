import Hypernets.Copying.CopyingInputContext
import Hypernets.Copying.CopyingInputIsomorphism
import Hypernets.Copying.CopyingTemplateEntry

/-! Every original input of a copying tree admits an actual Figure 17 rewrite.
The finite target retains the complete reordered original tree and restores the
external interface; no selected-spine or unused-branch assumption is needed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingSelectedInput
open Graph Combined

variable {d n k h : Nat} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (i : Fin (List.replicate (n+1) Wire.term).length)

def permutation : TypedPermutation (List.replicate (n+1) .term) :=
  CopyingInputPermutation.swap .term (n+1) ⟨0,by simp⟩ i

/-- Literal Figure 17 reduct for the selected original input, with the external
input reindexing cancelled after the rewrite. -/
noncomputable def after : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h) :=
  CopyingInputPermutation.net
    (CopyRule.after (CopyingInputPermutation.reordered T (permutation i)) H)
    (permutation i).symm

/-- The only rewrite used is the original local copying rule, transported
through a proved actual input-permutation context and a recursive isomorphism. -/
theorem rewrite (copyable : Copyable H) :
    Rewrite (CopyRule.before T H) (.input i) (after T H i) (.input i) := by
  have act := CopyingInputPermutation.rewrite (permutation i).symm
    ⟨0,by simp⟩ ⟨0,by simp⟩
    (Rewrite.local (Local.copy (CopyingInputPermutation.reordered T (permutation i)) H copyable))
  have selected : (permutation i).bijection.invFun ⟨0,by simp⟩ = i := by
    simp [permutation,CopyingInputPermutation.swap,CopyingInputPermutation.exchange]
  change Rewrite _ (.input ((permutation i).bijection.invFun ⟨0,by simp⟩)) _
    (.input ((permutation i).bijection.invFun ⟨0,by simp⟩)) at act
  rw [selected] at act
  exact act.rename (CopyingInputPermutation.beforeIso T H (permutation i)).symm (DeepIso.refl _)

/-- All original inputs have the same exact request/compute prefix: one search
transition followed by one genuine copying transition. -/
theorem entry (copyable : Copyable H) :
    (Combined.machine d (List.replicate (n+1) .term) (environmentInterface k h)).Steps 2
      ⟨CopyRule.before T H,(.search,.input i)⟩ ⟨after T H i,(.search,.input i)⟩ :=
  .cons (.search _ (CopyingTemplate.requests_copy T H i))
    (.cons (.rewrite (rewrite T H i copyable)) (.zero _))

end Hypernets.Copying.CopyingSelectedInput
