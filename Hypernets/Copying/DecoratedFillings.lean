import Hypernets.Copying.AtomicFillings

/-! Edgewise BPerm transformations and pointed residual certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
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
noncomputable def primitiveIso (full : PrimitiveFootprint G) : DeepIso G D.graph :=
  (identityIso G).symm.trans (Net.ExpansionIso.iso G (fun e => Classical.choice
    ((D.pair e).primitive_rigid (by intro _; obtain ⟨p,label⟩ := full e; exact ⟨p,label⟩))))

theorem primitiveIso_vertex (full : PrimitiveFootprint G) (v : G.Vertex) :
    Port.map (D.primitiveIso full).vertices.toFun v = Net.Expansion.host G D.fill v := by
  cases v <;> rfl
end Decoration

/-- A residual filling remembers the actual resumed token on both graphs. -/
structure PointedFilling {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  filling : FillingWitness template G H
  point : filling.context.Vertex
  left : (filling.leftPosition (.search,point)).2 = v
  right : (filling.rightPosition (.search,point)).2 = w

namespace PointedFilling
/-- Any boundary input gives a pointed residual, without a rootedness assumption. -/
def input {d I O} {G H : Hypernet d I O} (w : FillingWitness template G H) (i : Fin I.length) :
    PointedFilling G (.input i) H (.input i) := ⟨w,.input i,rfl,rfl⟩

/-- The reflexive certificate retains arbitrary internal or boundary token coordinates. -/
def refl {d I O} (G : Hypernet d I O) (free : FocusFree G) (v : G.Vertex) : PointedFilling G v G v := by
  refine ⟨FillingWitness.refl G free,v,?_,?_⟩ <;> cases v <;> rfl

/-- Changing either endpoint representation also transports its actual token. -/
def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : PointedFilling G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    PointedFilling A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) where
  filling := p.filling.congr f g
  point := p.point
  left := by
    change Port.map (n := I.length) (m := O.length) (f.vertices.toFun ∘ p.filling.leftIso.vertices.toFun)
      (Net.Expansion.host p.filling.context p.filling.left p.point) = _
    calc
      _ = Port.map f.vertices.toFun (p.filling.leftPosition (.search,p.point)).2 := by cases p.point <;> rfl
      _ = _ := congrArg (Port.map f.vertices.toFun) p.left
  right := by
    change Port.map (n := I.length) (m := O.length) (g.vertices.toFun ∘ p.filling.rightIso.vertices.toFun)
      (Net.Expansion.host p.filling.context p.filling.right p.point) = _
    calc
      _ = Port.map g.vertices.toFun (p.filling.rightPosition (.search,p.point)).2 := by cases p.point <;> rfl
      _ = _ := congrArg (Port.map g.vertices.toFun) p.right
end PointedFilling
end Hypernets.Copying.BoxPermutation
