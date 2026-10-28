import Hypernets.Copying.ContractionSpine
import Hypernets.Copying.LocalRewriteOccurrence

/-! A finite indexed selected path and its sibling wires realize the oriented
spine as a complete-label occurrence in the actual graph. No side subtree
belongs to this matched footprint. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionSpine
open Graph
variable {d I O} (G : Hypernet d I O) (s : ShareSort) (n : Nat)
    (orientation : Fin (n+1) → Bool) (edges : Fin (n+1) → G.Edge)
    (path : Fin (n+2) → G.Vertex) (sides : Fin (n+1) → G.Vertex)
    (injective : Function.Injective edges)
    (labels : ∀ e, G.edgeLabel (edges e) = primitiveLabel d (.contraction s))
    (source : ∀ e, G.source (edges e) = if orientation e then
      [sides e,path ⟨e.val,by omega⟩] else [path ⟨e.val,by omega⟩,sides e])
    (target : ∀ e, G.target (edges e) = [path ⟨e.val+1,by omega⟩])

/-- Exact ordered source/target equations construct a complete finite match. -/
def embedding : MatchEmbedding (atDepth s n orientation d) G where
  ports := ports s n path sides
  edges := edges
  edge_injective := injective
  primitive e p eq := by
    have equal : .contraction s = p := primitiveLabel_injective d eq
    subst p
    exact labels e
  source e := by
    rw [source]
    change (sources s n orientation e).map (ports s n path sides) = _
    unfold sources
    split <;> simp [ports_entry,ports_side]
  target e := by
    rw [target]
    change [ports s n path sides (out s n e)] = _
    rw [ports_out]

/-- All matched labels are primitive contractions, so the ordered embedding
already supplies the complete recursive-label occurrence. -/
noncomputable def occurrence : Opening.Occurrence (atDepth s n orientation d) G :=
  (embedding G s n orientation edges path sides injective labels source target).occurrence
    (fun e => by
      change LabelEquiv d (primitiveLabel d (.contraction s)) (G.edgeLabel (edges e))
      rw [labels]
      exact labelEquiv_refl d _)

theorem occurrence_input :
    (occurrence G s n orientation edges path sides injective labels source target).ports
      (.input ⟨0,by simp⟩) = path ⟨0,by omega⟩ := rfl

theorem occurrence_output :
    (occurrence G s n orientation edges path sides injective labels source target).ports (.output 0) =
      path ⟨n+1,by omega⟩ := rfl
end Hypernets.Copying.ContractionSpine
