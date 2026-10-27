import Hypernets.Copying.FullTranslationRenaming

/-! Put the original translated terms at a common representation allowance
before compensating their free-resource boundary action. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Padding the certified boundary action first gives the original padded
graphs directly, with no remaining heterogeneous depth cast at the endpoint. -/
theorem BoxPermutation.Renaming.paddedDerivation {k h d e}
    {ρ : Bijection (Fin k) (Fin k)} {α : Bijection (Fin h) (Fin h)}
    {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    (s : BoxPermutation.Renaming ρ α G H) (n : Nat) (dg : d ≤ n) (dh : e ≤ n) :
    BoxPermutation.Derivation (Translation.padTo n dg G)
      (InterfacePermutation.net (Translation.padTo n dh H)
        (TypedPermutation.environment ρ α).symm) := by
  obtain ⟨eq,derivation⟩ := (s.padTo n dg dh).derivation
  simpa only [Translation.castDepth] using derivation

/-- Full-syntax bijective renaming, at every common allowance and with the
free-variable and atom permutation explicitly undone outside the target. -/
theorem Translation.padded_term_rename_derivation {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (n : Nat) (bound : depth t ≤ n) :
    BoxPermutation.Derivation (padTo n bound (term t))
      (InterfacePermutation.net
        (padTo n (by rw [depth_rename]; exact bound) (term (Term.rename ρ.toFun α.toFun t)))
        (TypedPermutation.environment ρ α).symm) :=
  (term_rename_via_boxPermutation t ρ α).paddedDerivation n bound _

end Hypernets.Copying
