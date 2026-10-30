import Hypernets.Copying.BoxPullWeakeningReverseGeometry
import Hypernets.Copying.RetainedRewriteTransfer

/-! Actual nonweak primitive matches reflect from the decorated BPullW right
endpoint to the original source. The proof reconstructs the whole occurrence
and then applies the original local rewrite through its finite complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph
namespace Decoration
variable {d I O} {G : Hypernet d I O} (D : Decoration G)

theorem source_project (e : D.graph.Edge) {p : Primitive}
    (label : D.graph.edgeLabel e = primitiveLabel d p)
    (nonweak : ∀ s, p ≠ .weakening s) :
    (D.graph.source e).map D.project = G.source e.1 := by
  let c := D.rightPrimitiveCopy e.1 e.2 p label nonweak
  have eq := c.retained.source_eq (C := G) (H := D.fill)
  change D.graph.source ⟨e.1,c.edge⟩ = (G.source e.1).map (Net.Expansion.host G D.fill) at eq
  have ex : e = ⟨e.1,c.edge⟩ := by cases e; congr; exact c.only _
  rw [ex,eq,List.map_map]
  simp only [Function.comp_def,project_host]
  exact List.map_id _

theorem target_project (e : D.graph.Edge) {p : Primitive}
    (label : D.graph.edgeLabel e = primitiveLabel d p)
    (nonweak : ∀ s, p ≠ .weakening s) :
    (D.graph.target e).map D.project = G.target e.1 := by
  let c := D.rightPrimitiveCopy e.1 e.2 p label nonweak
  have eq := c.retained.target_eq (C := G) (H := D.fill)
  change D.graph.target ⟨e.1,c.edge⟩ = (G.target e.1).map (Net.Expansion.host G D.fill) at eq
  have ex : e = ⟨e.1,c.edge⟩ := by cases e; congr; exact c.only _
  rw [ex,eq,List.map_map]
  simp only [Function.comp_def,project_host]
  exact List.map_id _

/-- A rigid right contribution has only one edge, so its owner determines it. -/
theorem rigid_owner_injective (a b : D.graph.Edge) {p : Primitive}
    (label : D.graph.edgeLabel a = primitiveLabel d p)
    (nonweak : ∀ s, p ≠ .weakening s) (eq : a.1 = b.1) : a = b := by
  rcases a with ⟨e,a⟩
  rcases b with ⟨j,b⟩
  dsimp only at eq
  subst j
  let c := D.rightPrimitiveCopy e a p label nonweak
  exact congrArg (Sigma.mk e) ((c.only a).trans (c.only b).symm)

variable {J K} {A : Hypernet d J K} (f : MatchEmbedding A D.graph)
    (full : ∀ e, ∃ p, A.edgeLabel e = primitiveLabel d p ∧ ∀ s, p ≠ .weakening s)

include full in
/-- Injectivity is proved for the actual selected footprint. Two selected
nonweak edges cannot come from different pieces of the same shallow pair. -/
theorem right_owner_injective : Function.Injective (fun e => (f.edges e).1) := by
  intro a b eq
  apply f.edge_injective
  obtain ⟨p,ha,nonweak⟩ := full a
  exact D.rigid_owner_injective _ _ (f.primitive a p ha) nonweak eq

/-- Full ordered incidences are reflected, rather than only the active head. -/
def reflectPrimitive : MatchEmbedding A G where
  ports := D.project ∘ f.ports
  edges e := (f.edges e).1
  edge_injective := D.right_owner_injective f full
  primitive e p label := by
    obtain ⟨q,eq,nonweak⟩ := full e
    have same := primitiveLabel_injective d (label.symm.trans eq)
    subst q
    exact D.rightPrimitiveLabel _ _ p (f.primitive e p label) nonweak
  source e := by
    rw [← List.map_map,f.source]
    obtain ⟨p,label,nonweak⟩ := full e
    exact D.source_project _ (f.primitive e p label) nonweak
  target e := by
    rw [← List.map_map,f.target]
    obtain ⟨p,label,nonweak⟩ := full e
    exact D.target_project _ (f.primitive e p label) nonweak

noncomputable def reflectPrimitiveOccurrence : Opening.Occurrence A G :=
  (D.reflectPrimitive f full).occurrence
    ((D.reflectPrimitive f full).primitive_labels (fun e => by
      obtain ⟨p,label,_⟩ := full e
      exact ⟨p,label⟩))

include full in
/-- Every original local rule with this actual footprint is enabled at the
projected token on the left; its successor is constructed by the finite cut. -/
theorem primitive_enabled {B : Hypernet d J K} {v : A.Vertex} {w : B.Vertex}
    (step : Combined.Local A v B w) :
    ∃ H : Hypernet d I O, ∃ x, Combined.Rewrite G (D.project (f.ports v)) H x := by
  exact ⟨_,_,(D.reflectPrimitiveOccurrence f full).local_rewrite step⟩
end Decoration
end Hypernets.Copying.BoxPullWeakening
