import Hypernets.Copying.ApplicationOpeningLocal

/-! Source occurrences preserve recursive labels, including the box selected by beta. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening
open Graph

structure Occurrence {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K) where
  ports : G.Vertex → H.Vertex
  internals : G.Internal → H.Internal
  edges : G.Edge → H.Edge
  internal_map : ∀ x, ports (.internal x) = .internal (internals x)
  internal_injective : Function.Injective internals
  edge_injective : Function.Injective edges
  internal_label : ∀ x, H.internalLabel (internals x) = G.internalLabel x
  label : ∀ e, LabelEquiv d (G.edgeLabel e) (H.edgeLabel (edges e))
  source : ∀ e, (G.source e).map ports = H.source (edges e)
  target : ∀ e, (G.target e).map ports = H.target (edges e)

namespace Occurrence

def matchEmbedding {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K} (f : Occurrence G H) : MatchEmbedding G H where
  ports := f.ports
  edges := f.edges
  edge_injective := f.edge_injective
  primitive e p h := (Search.primitive_equiv (f.label e) p).mp h
  source := f.source
  target := f.target

def ofIso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : Occurrence G H where
  ports := Port.map f.vertices.toFun
  internals := f.vertices.toFun
  edges := f.edges.toFun
  internal_map _ := rfl
  internal_injective := fun _ _ h => f.vertices.injective h
  edge_injective := fun _ _ h => f.edges.injective h
  internal_label := f.internal_label
  label := f.edge_label
  source := f.source
  target := f.target

def plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole))) :
    Occurrence G (C.plug hole G) where
  ports := Net.Replacement.insert C hole G
  internals := Sum.inr
  edges := Sum.inr
  internal_map _ := rfl
  internal_injective := fun _ _ h => Sum.inr.inj h
  edge_injective := fun _ _ h => Sum.inr.inj h
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl

def expand {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) : Occurrence (F hole) (C.expand F) where
  ports := Net.Expansion.insert C F hole
  internals x := .inr ⟨hole,x⟩
  edges e := ⟨hole,e⟩
  internal_map _ := rfl
  internal_injective := fun _ _ h => eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
  edge_injective := fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl
end Occurrence
end Hypernets.Copying.Opening

namespace Hypernets.Copying.Application.Match
open Graph Opening MatchEmbedding
variable {d I O J K k h} {G : Hypernet (d+1) I O} {H : Hypernet (d+1) J K}
    {v} {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- An application occurrence transports the whole source match, including its box body. -/
def map (a : Match G v B) (f : Occurrence G H) : Match H (f.ports v) B where
  app := f.edges a.app
  lam := f.edges a.lam
  boxEdge := f.edges a.boxEdge
  functionWire := f.internals a.functionWire
  thunkWire := f.internals a.thunkWire
  argumentPort := f.ports a.argumentPort
  head_at := f.matchEmbedding.head a.head_at
  app_target := by rw [← f.target,a.app_target]; simp only [List.map_cons,List.map_nil,f.internal_map]
  lambda_label := (Search.primitive_equiv (f.label a.lam) _).mp a.lambda_label
  lambda_source := by rw [← f.source,a.lambda_source]; simp only [List.map_cons,List.map_nil,f.internal_map]
  lambda_target := by rw [← f.target,a.lambda_target]; simp only [List.map_cons,List.map_nil,f.internal_map]
  box_label := labelEquiv_trans _ (labelEquiv_symm _ (f.label a.boxEdge)) a.box_label
  box_source := by rw [← f.source,a.box_source]; simp only [List.map_cons,List.map_nil,f.internal_map]

/-- Extend the old-source attachment map by the identity on freshly exposed body vertices. -/
def originPort (f : Occurrence G H) :
    Port (G.Internal ⊕ (openBody B).Internal) I.length O.length →
    Port (H.Internal ⊕ (openBody B).Internal) J.length K.length
  | .internal (.inl x) => .internal (.inl (f.internals x))
  | .internal (.inr x) => .internal (.inr x)
  | .input i => Port.map Sum.inl (f.ports (.input i))
  | .output i => Port.map Sum.inl (f.ports (.output i))

theorem origin_old (f : Occurrence G H) (v : G.Vertex) :
    originPort (B := B) f (Port.map Sum.inl v) = Port.map Sum.inl (f.ports v) := by
  cases v <;> simp only [originPort,Port.map,f.internal_map]

theorem bodyPort_map (a : Match G v B) (f : Occurrence G H) (x : (openBody B).Vertex) :
    (a.map f).bodyPort x = originPort f (a.bodyPort x) := by
  cases x with
  | internal x => rfl
  | input i => exact (origin_old f v).symm
  | output i =>
    unfold bodyPort
    rw [origin_old]
    change Port.map Sum.inl ((f.ports a.argumentPort :: H.target (f.edges a.boxEdge))[i.val]'(by
      have length := (a.map f).output_length
      change (f.ports a.argumentPort :: H.target (f.edges a.boxEdge)).length = _ at length
      rw [length]; exact i.isLt)) = _
    simp only [← f.target,← List.map_cons,List.getElem_map]

end Hypernets.Copying.Application.Match
