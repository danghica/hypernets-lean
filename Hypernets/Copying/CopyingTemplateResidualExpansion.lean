import Hypernets.Copying.CopyingTemplateResidual
import Hypernets.Copying.BoxPullWeakeningResidualExpansion

/-! Closure of the two-link copying residual under arbitrary simultaneous
expansions. Original copying contributions remain in the first link. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined
open BoxPullWeakening (PointedWitness)
namespace Residual

/-- Untouched components keep their original certificates in the copying link,
and remain literal reflexive components during the sharing correction. -/
noncomputable def expandSelected {d I O} (C : Hypernet d I O)
    (G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (G e).Vertex} {w : (H e).Vertex} (p : Residual (G e) v (H e) w)
    (others : ∀ b, b ≠ e → FillingWitness template (G b) (H b)) :
    Residual (C.expand G) (Net.Expansion.insert C G e v)
      (C.expand H) (Net.Expansion.insert C H e w) := by
  let M := BoxPermutation.PointedFilling.replace C H e p.middle
  have middle : p.middle = M e := (BoxPermutation.PointedFilling.replace_selected C H e p.middle).symm
  let p0 := p.paired.cast rfl middle
  let p1 := p.correction.cast middle rfl
  have other0 (b) (ne : b ≠ e) : FillingWitness template (G b) (M b) := by
    simpa only [M,BoxPermutation.PointedFilling.replace_other C H e p.middle b ne] using others b ne
  have other1 (b) (ne : b ≠ e) : FillingWitness SharingTreeAlgebra.template (M b) (H b) := by
    simpa only [M,BoxPermutation.PointedFilling.replace_other C H e p.middle b ne] using
      FillingWitness.refl (T := SharingTreeAlgebra.template) (H b) (others b ne).focusFree.2
  refine ⟨C.expand M,Net.Expansion.insert C M e (PointedWitness.castVertex middle p.point),?_,?_⟩
  · have q := PointedWitness.expandSelected C G M e p0 other0
    simpa only [PointedWitness.castVertex_refl] using q
  · have q := PointedWitness.expandSelected C M H e p1 other1
    simpa only [PointedWitness.castVertex_refl] using q

/-- A selected actual rewrite and its two-link residual lift together through
a whole simultaneous expansion. The complement is the original derivation's
finite frame, with every other contribution explicitly retained. -/
theorem assemble {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (F e).Vertex} {w : (K e).Vertex}
    {H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {z : H.Vertex}
    (step : Rewrite (F e) v H z) (p : Residual (K e) w H z)
    (others : ∀ b, b ≠ e → FillingWitness template (K b) (F b)) :
    ∃ Q q, Rewrite (C.expand F) (Net.Expansion.insert C F e v) Q q ∧
      Nonempty (Residual (C.expand K) (Net.Expansion.insert C K e w) Q q) := by
  let J := BoxPermutation.PointedFilling.replace C F e H
  have build (H' : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (eq : J e = H')
      (z' : H'.Vertex) (s : Rewrite (F e) v H' z') (p' : Residual (K e) w H' z') :
      ∃ Q q, Rewrite (C.expand F) (Net.Expansion.insert C F e v) Q q ∧
        Nonempty (Residual (C.expand K) (Net.Expansion.insert C K e w) Q q) := by
    subst H'
    have other (b) (ne : b ≠ e) : FillingWitness template (K b) (J b) := by
      simpa only [J,BoxPermutation.PointedFilling.replace_other C F e H b ne] using others b ne
    exact ⟨C.expand J,Net.Expansion.insert C J e z',
      .expand C F J e (fun b ne => (BoxPermutation.PointedFilling.replace_other C F e H b ne).symm) s,
      ⟨expandSelected C K J e p' other⟩⟩
  exact build H (BoxPermutation.PointedFilling.replace_selected C F e H) z step p
end Residual
end Hypernets.Copying.CopyingTemplate
