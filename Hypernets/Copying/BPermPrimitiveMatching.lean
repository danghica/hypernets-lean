import Hypernets.Copying.BoxPermutationOrigins

/-! Any primitive-only operational occurrence in an arbitrary original BPerm
filling reflects to the context and has a matching occurrence on the other side. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

/-- The outer footprint is primitive; this does not constrain the enclosing graph. -/
def PrimitiveFootprint {d I O} (G : Hypernet d I O) : Prop :=
  ∀ e, ∃ p, G.edgeLabel e = primitiveLabel d p

namespace PrimitiveMatching
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (cert : ∀ e, DeepFillingEdge template C L R e)

def down : (C.expand L).Vertex → C.Vertex
  | .internal (.inl v) => .internal v
  | .internal (.inr ⟨e,v⟩) => False.elim ((component_no_internal (cert e)).1 v)
  | .input i => .input i
  | .output i => .output i

theorem down_host (v : C.Vertex) : down C cert (Net.Expansion.host C L v) = v := by cases v <;> rfl

theorem host_down (v : (C.expand L).Vertex) : Net.Expansion.host C L (down C cert v) = v := by
  cases v with
  | internal v => rcases v with v | ⟨e,v⟩; rfl; exact False.elim ((component_no_internal (cert e)).1 v)
  | input => rfl
  | output => rfl

theorem source_down (e : (C.expand L).Edge) {p}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p) :
    ((C.expand L).source e).map (down C cert) = C.source e.1 := by
  obtain ⟨l,r,old⟩ := primitive_retained (cert e.1) e.2 p label
  have eq := l.retained.source_eq
  change (C.expand L).source ⟨e.1,l.edge⟩ = (C.source e.1).map (Net.Expansion.host C L) at eq
  have ex : e = ⟨e.1,l.edge⟩ := by cases e; congr; exact l.only _
  rw [ex,eq,List.map_map]
  simp only [Function.comp_def,down_host]
  exact List.map_id _

theorem target_down (e : (C.expand L).Edge) {p}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p) :
    ((C.expand L).target e).map (down C cert) = C.target e.1 := by
  obtain ⟨l,r,old⟩ := primitive_retained (cert e.1) e.2 p label
  have eq := l.retained.target_eq
  change (C.expand L).target ⟨e.1,l.edge⟩ = (C.target e.1).map (Net.Expansion.host C L) at eq
  have ex : e = ⟨e.1,l.edge⟩ := by cases e; congr; exact l.only _
  rw [ex,eq,List.map_map]
  simp only [Function.comp_def,down_host]
  exact List.map_id _

variable {J K} {A : Hypernet d J K}
    (f : MatchEmbedding A (C.expand L)) (full : PrimitiveFootprint A)

/-- Reflect all ordered incidences, including possibly aliased boundary attachments. -/
def reflect : MatchEmbedding A C where
  ports := down C cert ∘ f.ports
  edges e := (f.edges e).1
  edge_injective := (owner_injective cert).comp f.edge_injective
  primitive e p label := (primitive_origin cert (f.edges e) p (f.primitive e p label)).1
  source e := by
    rw [← List.map_map,f.source]
    obtain ⟨p,label⟩ := full e
    exact source_down C cert _ (f.primitive e p label)
  target e := by
    rw [← List.map_map,f.target]
    obtain ⟨p,label⟩ := full e
    exact target_down C cert _ (f.primitive e p label)

noncomputable def rightCopy (e : A.Edge) : LabelCopy (R (f.edges e).1) (C.edgeLabel (f.edges e).1) :=
  Classical.choice (by
    obtain ⟨p,label⟩ := full e
    obtain ⟨l,r,_⟩ := primitive_retained (cert (f.edges e).1) (f.edges e).2 p (f.primitive e p label)
    exact ⟨r⟩)

/-- This is a constructed match, not an assumption that the redex transfers. -/
noncomputable def across : MatchEmbedding A (C.expand R) where
  ports := Net.Expansion.host C R ∘ (reflect C cert f full).ports
  edges e := ⟨(f.edges e).1,(rightCopy C cert f full e).edge⟩
  edge_injective := by
    intro e x eq
    have owners : (f.edges e).1 = (f.edges x).1 := congrArg (fun z : (C.expand R).Edge => z.1) eq
    exact (reflect C cert f full).edge_injective owners
  primitive e p label := (rightCopy C cert f full e).edge_label.trans
    ((reflect C cert f full).primitive e p label)
  source e := by
    rw [← List.map_map,(reflect C cert f full).source]
    exact (rightCopy C cert f full e).retained.source_eq.symm
  target e := by
    rw [← List.map_map,(reflect C cert f full).target]
    exact (rightCopy C cert f full e).retained.target_eq.symm

theorem across_host {v : A.Vertex} {x : C.Vertex}
    (attached : f.ports v = Net.Expansion.host C L x) :
    (across C cert f full).ports v = Net.Expansion.host C R x := by
  change Net.Expansion.host C R (down C cert (f.ports v)) = _
  rw [attached,down_host]

include cert full in
/-- Every edge of the matched footprint avoids shallow template replacement. -/
theorem avoids_shallow (e : A.Edge) (notHole : ∀ h, A.edgeLabel e ≠ primitiveLabel d (.hole h)) :
    ∀ h, C.edgeLabel (f.edges e).1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨p,label⟩ := full e
  intro h eq
  have bad := primitiveLabel_injective d (((reflect C cert f full).primitive e p label).symm.trans eq)
  subst p; exact notHole h label
end PrimitiveMatching
end Hypernets.Copying.BoxPermutation
