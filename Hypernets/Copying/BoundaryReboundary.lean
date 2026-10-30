import Hypernets.Copying.OccurrenceBoundaryCoverIso
import Hypernets.Copying.OccurrenceBoundaryTarget

/-! Literal equality transport of boundary isomorphisms, retaining the
actual port cast rather than identifying differently ordered interfaces. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryIso
open Graph Opening

/-- Interface equality changes only dependent port indices. -/
noncomputable def interfaceEquality {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K) :
    BoundaryIso G (G.reboundary hi ho) :=
  ((Occurrence.ofIso (DeepIso.refl G)).reboundaryTarget hi ho).boundaryIso_of_edge_surjective
    (by intro i; trivial) (by intro i; trivial) (by intro e; exact ⟨e,rfl⟩)

theorem interfaceEquality_port {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K) (v : G.Vertex) :
    (interfaceEquality G hi ho).ports.toFun v = Port.cast hi ho v := by
  change Port.cast hi ho (Port.map id v) = _
  cases v <;> rfl

/-- Simultaneous source/target interface equalities preserve the explicit
boundary action by the corresponding input/output casts. -/
noncomputable def reboundaryBoth {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) :
    BoundaryIso (G.reboundary hi ho) (H.reboundary hj hk) :=
  (interfaceEquality G hi ho).symm.trans (f.trans (interfaceEquality H hj hk))

end Hypernets.Copying.BoundaryIso
