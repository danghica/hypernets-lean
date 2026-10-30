import Hypernets.Copying.BoxPullContractionAtomic

/-! Edgewise BPullC transformations and pointed residual certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

/-- Replace each original edge by an atomically certified contribution. -/
structure Decoration {d I O} (G : Hypernet d I O) where
  fill : (e : G.Edge) → Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
    ((alphabet d).signature.output (G.edgeLabel e))
  pair : ∀ e, AtomicPair (Net.corolla (alphabet d).signature (G.edgeLabel e)) (fill e)

namespace Decoration
variable {d I O} {G : Hypernet d I O} (D : Decoration G)

abbrev graph := G.expand D.fill

def identity (G : Hypernet d I O) : Decoration G where
  fill e := Net.corolla (alphabet d).signature (G.edgeLabel e)
  pair _ := .iso (DeepIso.refl _)

def identityIso (G : Hypernet d I O) : DeepIso (identity G).graph G :=
  DeepIso.ofIso (FillingCollapse.identity G _ (fun _ => LabelCopy.corolla _))

/-- Edgewise witnesses assemble to the original recursive filling relation. -/
noncomputable def witness (free : FocusFree G) : FillingWitness template G D.graph :=
  (FillingWitness.expand G (fun e => (D.pair e).witness (fun _ => free e))).congr
    (identityIso G) (DeepIso.refl _)

/-- Every primitive source edge is unchanged up to ordered recursive naming. -/
noncomputable def primitiveIso (full : BoxPermutation.PrimitiveFootprint G) : DeepIso G D.graph :=
  (identityIso G).symm.trans (Net.ExpansionIso.iso G (fun e => Classical.choice
    ((D.pair e).primitive_rigid (by intro _; obtain ⟨p,label⟩ := full e; exact ⟨p,label⟩))))

theorem primitiveIso_vertex (full : BoxPermutation.PrimitiveFootprint G) (v : G.Vertex) :
    Port.map (D.primitiveIso full).vertices.toFun v = Net.Expansion.host G D.fill v := by
  cases v <;> rfl
end Decoration

end Hypernets.Copying.BoxPullContraction
