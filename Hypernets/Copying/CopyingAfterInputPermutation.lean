import Hypernets.Copying.CopyingInputContext
import Hypernets.Copying.CopyingInputIsomorphism
import Hypernets.Copying.CopyCoherence

/-! Input permutations fixing the selected input commute with the original
copy reduct. Both comparisons are actual copies, so proved successor coherence
supplies a recursive graph isomorphism without modifying any local rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph Combined

/-- Reindex the complete original source, keeping every payload edge and
ordered output, before invoking either actual copy transition. -/
noncomputable def beforeReorderedIso {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (p : TypedPermutation (List.replicate (n+1) .term)) :
    DeepIso (net (CopyRule.before T H) p) (CopyRule.before (reordered T p) H) := by
  have first := congr (beforeIso T H p) p
  have last := (roundtrip (CopyRule.before (reordered T p) H) p.symm).symm
  exact first.trans last

/-- For every original copyable payload, a permutation fixing input zero
preserves the literal copy reduct up to recursive graph representation. -/
noncomputable def afterIso {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (p : TypedPermutation (List.replicate (n+1) .term))
    (fixed : p.bijection.toFun ⟨0,by simp⟩ = ⟨0,by simp⟩) :
    DeepIso (net (CopyRule.after T H) p) (CopyRule.after (reordered T p) H) := by
  have first := rewrite p ⟨0,by simp⟩ ⟨0,by simp⟩
    (Rewrite.local (.copy T H copyable))
  rw [fixed] at first
  have actual := first.rename (beforeReorderedIso T H p) (DeepIso.refl _)
  have left : Rewrite (CopyRule.before (reordered T p) H) (.input ⟨0,by simp⟩)
      (net (CopyRule.after T H) p) (.input ⟨0,by simp⟩) := by
    simpa only [Port.map] using actual
  exact (Classical.choice (rewrite_deterministic left (.local (.copy (reordered T p) H copyable)))).graph

end Hypernets.Copying.CopyingInputPermutation
