import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.BoxPullWeakeningViews
import Hypernets.Copying.BoxPullWeakeningNormalization

/-! Reverse provenance of actual BPullW right-hand edges. The separate
weakening has no source, and all other primitive occurrences are rigid. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph

namespace AtomicPair
/-- A corolla source never acquires internal vertices by BPullW. The shallow
right contribution consists of the box and a disconnected weakening. -/
theorem right_no_internal {d I O} {G H : Hypernet d I O} (pair : AtomicPair G H)
    (empty : ∀ _v : G.Internal, False) (v : H.Internal) : False := by
  induction pair with
  | iso f => exact empty (f.vertices.invFun v)
  | shallow rel =>
    cases rel with
    | witness l step r =>
      cases step with
      | @pull d n k h B s free =>
        rcases r.vertices.invFun v with ⟨b,x⟩
        cases b <;> exact nomatch x
  | boxed body => exact nomatch v
  | @congr d I O G H A B f pair g ih =>
    exact ih (fun x => empty (f.vertices.invFun x)) (g.vertices.invFun v)
  | interfaces hi ho pair ih =>
    cases hi; cases ho
    exact ih empty v

/-- A primitive edge other than weakening cannot originate in a changed box.
Its complete contribution is therefore an actual recursive isomorphism. -/
theorem right_primitive_rigid {d I O} {G H : Hypernet d I O} (pair : AtomicPair G H)
    (e : H.Edge) (p : Primitive) (label : H.edgeLabel e = primitiveLabel d p)
    (nonweak : ∀ s, p ≠ .weakening s) : Nonempty (DeepIso G H) := by
  induction pair with
  | iso f => exact ⟨f⟩
  | shallow rel =>
    cases rel with
    | witness l step r =>
      cases step with
      | @pull d n k h B s free =>
        have eq : (right B s).edgeLabel (r.edges.invFun e) = primitiveLabel _ p :=
          (Search.primitive_equiv (r.edge_label (r.edges.invFun e)) p).mpr
            (by simpa only [r.edges.right_inv] using label)
        generalize hx : r.edges.invFun e = z at eq
        rcases z with ⟨b,x⟩
        cases b
        · cases eq
        · let c := Opening.Occurrence.primitiveCopy (d+1) (.weakening s)
          have hx := congrArg (primitiveNet (d+1) (.weakening s)).edgeLabel (c.only x)
          have prim : primitiveLabel (d+1) (.weakening s) = primitiveLabel (d+1) p :=
            (hx.trans c.edge_label).symm.trans eq
          exact False.elim (nonweak s (primitiveLabel_injective _ prim).symm)
  | boxed body => cases label
  | @congr d I O G H A B f pair g ih =>
    have eq : H.edgeLabel (g.edges.invFun e) = primitiveLabel d p :=
      (Search.primitive_equiv (g.edge_label (g.edges.invFun e)) p).mpr
        (by simpa only [g.edges.right_inv] using label)
    obtain ⟨h⟩ := ih (g.edges.invFun e) eq
    exact ⟨f.trans (h.trans g)⟩
  | interfaces hi ho pair ih =>
    cases hi; cases ho
    simpa only [Net.reboundary_refl] using ih e label
end AtomicPair

namespace Decoration
variable {d I O} {G : Hypernet d I O} (D : Decoration G)

/-- The source and decorated right graph have the same original vertices.
Only edge contributions can split; no fresh internal coordinate is introduced. -/
def rightVertices : Bijection D.graph.Internal G.Internal where
  toFun
    | .inl v => v
    | .inr ⟨e,v⟩ => False.elim ((D.pair e).right_no_internal (fun x => nomatch x) v)
  invFun := Sum.inl
  left_inv v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · exact False.elim ((D.pair e).right_no_internal (fun x => nomatch x) v)
  right_inv _ := rfl

def project (v : D.graph.Vertex) : G.Vertex := Port.map D.rightVertices.toFun v

theorem project_host (v : G.Vertex) : D.project (Net.Expansion.host G D.fill v) = v := by
  cases v <;> rfl

theorem host_project (v : D.graph.Vertex) : Net.Expansion.host G D.fill (D.project v) = v := by
  cases v with
  | input _ => rfl
  | output _ => rfl
  | internal v => exact congrArg Port.internal (D.rightVertices.left_inv v)

/-- Every actual nonweak primitive on the right belongs to a wholly rigid
source corolla; the separately introduced weakening is explicitly excluded. -/
noncomputable def rightPrimitiveIso (e : G.Edge) (x : (D.fill e).Edge) (p : Primitive)
    (label : (D.fill e).edgeLabel x = primitiveLabel d p) (nonweak : ∀ s, p ≠ .weakening s) :
    DeepIso (Net.corolla (alphabet d).signature (G.edgeLabel e)) (D.fill e) :=
  Classical.choice ((D.pair e).right_primitive_rigid x p label nonweak)

/-- The rigid component's actual primitive label equals its source label. -/
theorem rightPrimitiveLabel (e : G.Edge) (x : (D.fill e).Edge) (p : Primitive)
    (label : (D.fill e).edgeLabel x = primitiveLabel d p) (nonweak : ∀ s, p ≠ .weakening s) :
    G.edgeLabel e = primitiveLabel d p := by
  let f := D.rightPrimitiveIso e x p label nonweak
  have eq := (Search.primitive_equiv (f.edge_label (f.edges.invFun x)) p).mpr
    (by simpa only [f.edges.right_inv] using label)
  exact eq

/-- Retain the exact ordered input/output corolla data of the rigid component. -/
noncomputable def rightPrimitiveCopy (e : G.Edge) (x : (D.fill e).Edge) (p : Primitive)
    (label : (D.fill e).edgeLabel x = primitiveLabel d p) (nonweak : ∀ s, p ≠ .weakening s) :
    LabelCopy (D.fill e) (G.edgeLabel e) := by
  let f := D.rightPrimitiveIso e x p label nonweak
  let c := (LabelCopy.corolla (G.edgeLabel e)).ofIso f.symm
  refine { c with edge_label := ?_ }
  exact (congrArg (D.fill e).edgeLabel (c.only x).symm).trans
    (label.trans (D.rightPrimitiveLabel e x p label nonweak).symm)
end Decoration
end Hypernets.Copying.BoxPullWeakening
