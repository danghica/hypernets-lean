import Hypernets.Copying.PrimitiveContextOccurrence

/-! An equal ordered host interface transports an entire occurrence without
changing its edges or internal injection. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph

def reboundaryTarget {d I O J K P Q} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : Occurrence G H) (hi : J = P) (ho : K = Q) :
    Occurrence G (H.reboundary hi ho) where
  ports v := Port.cast hi ho (f.ports v)
  internals := f.internals
  edges := f.edges
  internal_map x := by rw [f.internal_map]; rfl
  internal_injective := f.internal_injective
  edge_injective := f.edge_injective
  internal_label := f.internal_label
  label := f.label
  source e := by change (G.source e).map _ = (H.source (f.edges e)).map _; rw [← f.source,List.map_map]; rfl
  target e := by change (G.target e).map _ = (H.target (f.edges e)).map _; rw [← f.target,List.map_map]; rfl

end Hypernets.Copying.Opening.Occurrence
