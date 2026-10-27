import Hypernets.Copying.BetaResidualExamples

/-! Exhaustive outer-edge provenance for original BPerm recursive fillings.
Shallow replacements are single box edges, never primitive redex edges. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

/-- This restriction concerns outer labels only; box bodies are arbitrary. -/
def NoOuterPrimitive {d I O} (G : Hypernet d I O) : Prop :=
  ∀ e p, G.edgeLabel e ≠ primitiveLabel d p

/-- Both sides of every genuine, independently represented BPerm pair have one
outer edge, no internal vertices and no outer primitive label. -/
theorem UpToIso.outer_shape {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    (∀ x y : G.Edge, x = y) ∧ (∀ x y : H.Edge, x = y) ∧
    (∀ v : G.Internal, False) ∧ (∀ v : H.Internal, False) ∧
    NoOuterPrimitive G ∧ NoOuterPrimitive H := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | permute B p =>
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · intro x y; apply f.edges.injective; exact Fin.ext (by have := (f.edges.toFun x).isLt; have := (f.edges.toFun y).isLt; omega)
      · intro x y; apply g.edges.symm.injective; exact Fin.ext (by have := (g.edges.invFun x).isLt; have := (g.edges.invFun y).isLt; omega)
      · intro v; cases f.vertices.toFun v
      · intro v; cases g.vertices.invFun v
      · intro e a label
        have bad := f.edge_label e
        rw [label] at bad
        exact bad
      · intro e a label
        have bad := g.symm.edge_label e
        rw [label] at bad
        exact bad

variable {d I O} {C : Hypernet d I O} {L R}

/-- Any primitive edge in either actual filling was retained from the original
context. This includes operations, contractions, weakening, instances and stores. -/
theorem primitive_retained {e} (edge : DeepFillingEdge template C L R e)
    (x : (L e).Edge) (p : Primitive) (label : (L e).edgeLabel x = primitiveLabel d p) :
    ∃ l : LabelCopy (L e) (C.edgeLabel e),
      ∃ r : LabelCopy (R e) (C.edgeLabel e), C.edgeLabel e = primitiveLabel d p := by
  cases edge with
  | retained l r => exact ⟨l,r,l.edge_label.symm.trans ((congrArg (L e).edgeLabel (l.only x).symm).trans label)⟩
  | filled h hole rel => exact False.elim (rel.1.outer_shape.2.2.2.2.1 x p label)
  | boxed b old inner l r =>
    have eq := l.edge_label.symm.trans ((congrArg (L e).edgeLabel (l.only x).symm).trans label)
    cases eq

/-- Every filling component has exactly one outer edge, even at a shallow hole. -/
theorem component_singleton {e} (edge : DeepFillingEdge template C L R e) :
    (∀ x y : (L e).Edge, x = y) ∧ (∀ x y : (R e).Edge, x = y) := by
  cases edge with
  | retained l r => exact ⟨fun x y => (l.only x).trans (l.only y).symm,fun x y => (r.only x).trans (r.only y).symm⟩
  | filled h label rel => exact ⟨rel.1.outer_shape.1,rel.1.outer_shape.2.1⟩
  | boxed b label inner l r => exact ⟨fun x y => (l.only x).trans (l.only y).symm,fun x y => (r.only x).trans (r.only y).symm⟩

theorem component_no_internal {e} (edge : DeepFillingEdge template C L R e) :
    (∀ v : (L e).Internal, False) ∧ (∀ v : (R e).Internal, False) := by
  cases edge with
  | retained l r => exact ⟨l.no_internal,r.no_internal⟩
  | filled h label rel => exact ⟨rel.1.outer_shape.2.2.1,rel.1.outer_shape.2.2.2.1⟩
  | boxed b label inner l r => exact ⟨l.no_internal,r.no_internal⟩

/-- Thus projecting actual edges to their original context owner is injective. -/
theorem owner_injective (edges : ∀ e, DeepFillingEdge template C L R e) :
    Function.Injective (fun e : (C.expand L).Edge => e.1) := by
  rintro ⟨e,x⟩ ⟨f,y⟩ eq
  dsimp at eq; subst f
  exact congrArg (Sigma.mk e) ((component_singleton (edges e)).1 x y)

/-- Every actual vertex is an original host coordinate; no shallow replacement
can hide a newly allocated outer wire in a BPerm specimen. -/
theorem vertex_origin (edges : ∀ e, DeepFillingEdge template C L R e)
    (v : (C.expand L).Vertex) : ∃ x : C.Vertex, Net.Expansion.host C L x = v := by
  cases v with
  | internal v =>
    rcases v with v | ⟨e,v⟩
    · exact ⟨.internal v,rfl⟩
    · exact False.elim ((component_no_internal (edges e)).1 v)
  | input i => exact ⟨.input i,rfl⟩
  | output i => exact ⟨.output i,rfl⟩

/-- Primitive provenance is independent of any chosen operational match. -/
theorem primitive_origin (edges : ∀ e, DeepFillingEdge template C L R e)
    (e : (C.expand L).Edge) (p : Primitive)
    (label : (C.expand L).edgeLabel e = primitiveLabel d p) :
    C.edgeLabel e.1 = primitiveLabel d p ∧
    Nonempty (LabelCopy (L e.1) (C.edgeLabel e.1) × LabelCopy (R e.1) (C.edgeLabel e.1)) := by
  obtain ⟨l,r,old⟩ := primitive_retained (edges e.1) e.2 p label
  exact ⟨old,⟨l,r⟩⟩
end Hypernets.Copying.BoxPermutation
