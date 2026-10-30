import Hypernets.Copying.BoxPullContractionCoordinates
import Hypernets.Copying.CombinedPadding

/-! Transport an actual rewrite through the literal output-contraction frame.
This uses the existing simultaneous-context expansion rule, with its separate
contraction edge unchanged. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined

/-- Boundary-to-boundary rewrites preserve the two external contraction
junctions and resume at exactly the original input coordinate. -/
theorem merge_rewrite {d I A B} (s : ShareSort)
    {G H : Hypernet d I (A ++ s.wire :: s.wire :: B)} (i j : Fin I.length)
    (step : Rewrite G (.input i) H (.input j)) :
    Rewrite (merge s G) (.input i) (merge s H) (.input j) := by
  cases d
  all_goals
    have lifted := Rewrite.expand (pattern _ I A B s) (filling s G) (filling s H) false
      (by intro b hb; cases b; exact False.elim (hb rfl); rfl) step
    change Rewrite (merge s G) _ (merge s H) _ at lifted
    simpa [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,pattern,frame,frameSource,
      List.getElem_map,Port.map] using lifted

/-- A full graph isomorphism of the payload extends through the unchanged
output contraction and preserves its ordered interface. -/
def merge_congr {d I A B} (s : ShareSort) {G H : Hypernet d I (A ++ s.wire :: s.wire :: B)}
    (f : DeepIso G H) : DeepIso (merge s G) (merge s H) := by
  cases d
  all_goals
    exact Net.ExpansionIso.iso (pattern _ I A B s) (F := filling s G) (K := filling s H)
      (fun b => by cases b; exact f; exact DeepIso.refl _)

end Hypernets.Copying.BoxPullContraction
