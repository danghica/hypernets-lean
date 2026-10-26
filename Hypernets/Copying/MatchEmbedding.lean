import Hypernets.Copying.LoweringExamples

/-! Incidence-preserving occurrences used to compare independently chosen matches.
Boundary ports may be identified on attachment; edge occurrences remain distinct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- An outer graph occurrence, allowing boundary attachment and a changed depth allowance. -/
structure MatchEmbedding {d r I O J K} (G : Hypernet d I O) (H : Hypernet r J K) where
  ports : G.Vertex → H.Vertex
  edges : G.Edge → H.Edge
  edge_injective : Function.Injective edges
  primitive : ∀ e p, G.edgeLabel e = primitiveLabel d p → H.edgeLabel (edges e) = primitiveLabel r p
  source : ∀ e, (G.source e).map ports = H.source (edges e)
  target : ∀ e, (G.target e).map ports = H.target (edges e)

namespace MatchEmbedding

def refl {d I O} (G : Hypernet d I O) : MatchEmbedding G G where
  ports := id
  edges := id
  edge_injective := fun _ _ h => h
  primitive _ _ h := h
  source _ := List.map_id _
  target _ := List.map_id _

def comp {d r s I O J K L M} {G : Hypernet d I O} {H : Hypernet r J K} {N : Hypernet s L M}
    (f : MatchEmbedding G H) (g : MatchEmbedding H N) : MatchEmbedding G N where
  ports := g.ports ∘ f.ports
  edges := g.edges ∘ f.edges
  edge_injective := g.edge_injective.comp f.edge_injective
  primitive e p h := g.primitive _ p (f.primitive e p h)
  source e := by rw [← List.map_map, f.source, g.source]; rfl
  target e := by rw [← List.map_map, f.target, g.target]; rfl

def ofTransport {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K} (f : Search.Transport G H) : MatchEmbedding G H where
  ports := f.ports.toFun
  edges := f.edges.toFun
  edge_injective := fun _ _ h => f.edges.injective h
  primitive e p := (f.primitive e p).mp
  source := f.source
  target := f.target

def ofDeepIso {d I O} {G : Hypernet d I O} {H : Hypernet d I O} (f : DeepIso G H) : MatchEmbedding G H :=
  ofTransport (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f))

def plug {d I O} (C : Hypernet d I O) (e : C.Edge)
    (F : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) : MatchEmbedding F (C.plug e F) where
  ports := Net.Replacement.insert C e F
  edges := Sum.inr
  edge_injective := fun _ _ h => Sum.inr.inj h
  primitive _ _ h := h
  source _ := rfl
  target _ := rfl

def expand {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge) : MatchEmbedding (F e) (C.expand F) where
  ports := Net.Expansion.insert C F e
  edges b := ⟨e,b⟩
  edge_injective := fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  primitive _ _ h := h
  source _ := rfl
  target _ := rfl

def serialLeft {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) : MatchEmbedding G (Serial.net G H) where
  ports := BoundarySerial.leftInsert G H
  edges := Serial.leftEdge G H
  edge_injective := by cases d <;> intro _ _ h <;> exact eq_of_heq (Sigma.mk.inj h).2
  primitive e p h := (Serial.leftEdge_label G H e).trans h
  source e := by cases d <;> rfl
  target e := by cases d <;> rfl

def serialRight {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) : MatchEmbedding H (Serial.net G H) where
  ports := BoundarySerial.rightInsert G H
  edges := Serial.rightEdge G H
  edge_injective := by cases d <;> intro _ _ h <;> exact eq_of_heq (Sigma.mk.inj h).2
  primitive e p h := (Serial.rightEdge_label G H e).trans h
  source e := by cases d <;> rfl
  target e := by cases d <;> rfl

variable {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}

theorem source_mem (f : MatchEmbedding G H) {v e} (h : v ∈ G.source e) :
    f.ports v ∈ H.source (f.edges e) := by
  rw [← f.source]; exact List.mem_map_of_mem h

theorem target_mem (f : MatchEmbedding G H) {v e} (h : v ∈ G.target e) :
    f.ports v ∈ H.target (f.edges e) := by
  rw [← f.target]; exact List.mem_map_of_mem h

theorem adjacent (f : MatchEmbedding G H) {a b} (h : G.Adjacent a b) : H.Adjacent (f.edges a) (f.edges b) := by
  obtain ⟨v,ha,hb⟩ := h
  exact ⟨f.ports v,f.target_mem ha,f.source_mem hb⟩

/-- A primitive edge consuming the focused wire is intrinsic to the host graph. -/
def HeadAt (G : Hypernet d I O) (v : G.Vertex) (e : G.Edge) (p : Primitive) : Prop :=
  G.edgeLabel e = primitiveLabel d p ∧ v ∈ G.source e

theorem head_unique {v a b p q} (ha : HeadAt G v a p) (hb : HeadAt G v b q) : a = b ∧ p = q := by
  have eq := G.source_unique ha.2 hb.2
  refine ⟨eq,?_⟩
  apply primitiveLabel_injective d
  exact ha.1.symm.trans (eq ▸ hb.1)

theorem head (f : MatchEmbedding G H) {v e p} (h : HeadAt G v e p) :
    HeadAt H (f.ports v) (f.edges e) p := ⟨f.primitive e p h.1,f.source_mem h.2⟩

/-- Ordered argument matching is fixed by the host incidence lists. -/
def Argument (G : Hypernet d I O) (e : G.Edge) (i : Nat) (a : G.Edge) : Prop :=
  ∃ v, (G.target e)[i]? = some v ∧ v ∈ G.source a

theorem argument_unique {e i a b} (ha : Argument G e i a) (hb : Argument G e i b) : a = b := by
  obtain ⟨v,hv,ha⟩ := ha
  obtain ⟨w,hw,hb⟩ := hb
  have eq : v = w := Option.some.inj (hv.symm.trans hw)
  exact G.source_unique ha (eq ▸ hb)

theorem argument (f : MatchEmbedding G H) {e i a} (h : Argument G e i a) :
    Argument H (f.edges e) i (f.edges a) := by
  obtain ⟨v,hv,ha⟩ := h
  refine ⟨f.ports v,?_,f.source_mem ha⟩
  rw [← f.target,List.getElem?_map,hv]; rfl
end MatchEmbedding
end Hypernets.Copying
