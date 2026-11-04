import Hypernets.Copying.CopyingInputPermutation
import Hypernets.Graph.Simultaneous

/-! Input reindexing commutes with expansion by the identical original
component family. Only external boundary occurrences move. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph
variable {d I O} (G : Hypernet d I O) (p : TypedPermutation I)
    (F : (e : G.Edge) → Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e)))

theorem expansion_insert (e : G.Edge) (v : (F e).Vertex) :
    Net.Expansion.insert (net G p) F e v =
      (ports (G.expand F) p).toFun (Net.Expansion.insert G F e v) := by
  cases v with
  | internal a => rfl
  | input i =>
    change Net.Expansion.host (net G p) F (((G.source e).map (ports G p).toFun)[i.val]'(by rw [List.length_map,G.source_length];exact i.isLt)) = _
    rw [List.getElem_map]
    change Net.Expansion.host (net G p) F ((ports G p).toFun (G.sourcePort e i)) =
      (ports (G.expand F) p).toFun (Net.Expansion.host G F (G.sourcePort e i))
    cases G.sourcePort e i <;> rfl
  | output i =>
    change Net.Expansion.host (net G p) F (((G.target e).map (ports G p).toFun)[i.val]'(by rw [List.length_map,G.target_length];exact i.isLt)) = _
    rw [List.getElem_map]
    change Net.Expansion.host (net G p) F ((ports G p).toFun (G.targetPort e i)) =
      (ports (G.expand F) p).toFun (Net.Expansion.host G F (G.targetPort e i))
    cases G.targetPort e i <;> rfl

/-- The isomorphism is the identity on all original and inserted internal
vertices and edges, with the external action already recorded in the target. -/
def expansionIso : DeepIso ((net G p).expand F) (net (G.expand F) p) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := labelEquiv_refl d _
  source e := by
    change (((F e.1).source e.2).map (Net.Expansion.insert (net G p) F e.1)).map (Port.map id) =
      (((F e.1).source e.2).map (Net.Expansion.insert G F e.1)).map (ports (G.expand F) p).toFun
    simp only [Port.map_id_fun,List.map_map]
    exact List.map_congr_left (fun v _ => expansion_insert G p F e.1 v)
  target e := by
    change (((F e.1).target e.2).map (Net.Expansion.insert (net G p) F e.1)).map (Port.map id) =
      (((F e.1).target e.2).map (Net.Expansion.insert G F e.1)).map (ports (G.expand F) p).toFun
    simp only [Port.map_id_fun,List.map_map]
    exact List.map_congr_left (fun v _ => expansion_insert G p F e.1 v)

end Hypernets.Copying.CopyingInputPermutation
