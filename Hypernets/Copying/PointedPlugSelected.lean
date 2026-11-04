import Hypernets.Copying.BoxPullWeakeningResidualExpansion
import Hypernets.Copying.CopyingInputContext

/-! An actual pointed filling lifts at its selected component coordinate,
including arbitrary internal positions, through an original plugging context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph Combined

noncomputable def plugSelected {T : PreTemplate} {d I O} (C : Hypernet d I O)
    (free : FocusFree C) (e : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {v w}
    (p : PointedWitness T G v H w) :
    PointedWitness T (C.plug e G) (Net.Replacement.insert C e G v)
      (C.plug e H) (Net.Replacement.insert C e H w) := by
  let F := SingleExpansion.family C e G
  let K := SingleExpansion.family C e H
  have aux (A B) (ha : F e = A) (hb : K e = B) (a : A.Vertex) (b : B.Vertex)
      (q : PointedWitness T A a B b) :
      PointedWitness T (C.plug e A) (Net.Replacement.insert C e A a)
        (C.plug e B) (Net.Replacement.insert C e B b) := by
    subst A; subst B
    have others (x) (ne : x ≠ e) : FillingWitness T (F x) (K x) := by
      have le := SingleExpansion.retained C e G x ne
      have re := SingleExpansion.retained C e H x ne
      exact FillingWitness.of_copies le re (le.focusFree (free x))
    have total := expandSelected C F K e q others
    have moved := total.congr (ExpandedRewrite.peel C F e (SingleExpansion.retained C e G))
      (ExpandedRewrite.peel C K e (SingleExpansion.retained C e H))
    rw [ExpandedRewrite.peel_insert,ExpandedRewrite.peel_insert] at moved
    exact moved
  exact aux G H (SingleExpansion.selected C e G) (SingleExpansion.selected C e H) v w p

end Hypernets.Copying.BoxPullWeakening.PointedWitness
