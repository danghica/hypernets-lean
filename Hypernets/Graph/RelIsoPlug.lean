import Hypernets.Graph.RelIso

/-! Shallow plugging respects any reflexive relation on edge labels. -/

namespace Hypernets.Graph.Net

universe u

namespace RelIsoPlug

variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R : Op → Op → Prop} (C : Net σ I O) (hole : C.Edge)
    {H K : Net σ (σ.input (C.edgeLabel hole)) (σ.output (C.edgeLabel hole))}
    (f : RelIso R H K)

def vertices : Bijection (C.Internal ⊕ H.Internal) (C.Internal ⊕ K.Internal) :=
  (Bijection.refl C.Internal).sum f.vertices

def edges : Bijection (Replacement.Edge C hole H) (Replacement.Edge C hole K) :=
  (Bijection.refl {e : C.Edge // e ≠ hole}).sum f.edges

theorem map_host (v : C.Vertex) :
    Port.map (vertices C hole f).toFun (Replacement.host C hole H v) = Replacement.host C hole K v := by
  cases v <;> rfl

theorem map_insert (v : H.Vertex) :
    Port.map (vertices C hole f).toFun (Replacement.insert C hole H v) =
      Replacement.insert C hole K (Port.map f.vertices.toFun v) := by
  cases v with
  | internal v => rfl
  | input i => exact map_host C hole f _
  | output i => exact map_host C hole f _

end RelIsoPlug

/-- Isomorphic replacements produce isomorphic whole graphs in every shallow
typed context, without a non-self-loop restriction on the hole. -/
def RelIso.plug {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R : Op → Op → Prop} (C : Net σ I O) (hole : C.Edge)
    {H K : Net σ (σ.input (C.edgeLabel hole)) (σ.output (C.edgeLabel hole))}
    (reflexive : ∀ a, R a a) (f : RelIso R H K) : RelIso R (C.plug hole H) (C.plug hole K) where
  vertices := RelIsoPlug.vertices C hole f
  edges := RelIsoPlug.edges C hole f
  internal_label v := by
    cases v with
    | inl v => rfl
    | inr v => exact f.internal_label v
  edge_label e := by
    cases e with
    | inl e => exact reflexive _
    | inr e => exact f.edge_label e
  source e := by
    cases e with
    | inl e =>
        change ((C.source e.val).map (Replacement.host C hole H)).map
          (Port.map (RelIsoPlug.vertices C hole f).toFun) =
          (C.source e.val).map (Replacement.host C hole K)
        simp only [List.map_map]
        congr 1; funext v; exact RelIsoPlug.map_host C hole f v
    | inr e =>
        change ((H.source e).map (Replacement.insert C hole H)).map
          (Port.map (RelIsoPlug.vertices C hole f).toFun) =
          (K.source (f.edges.toFun e)).map (Replacement.insert C hole K)
        calc
          _ = ((H.source e).map (Port.map f.vertices.toFun)).map (Replacement.insert C hole K) := by
            simp only [List.map_map]
            congr 1; funext v; exact RelIsoPlug.map_insert C hole f v
          _ = _ := by rw [f.source]
  target e := by
    cases e with
    | inl e =>
        change ((C.target e.val).map (Replacement.host C hole H)).map
          (Port.map (RelIsoPlug.vertices C hole f).toFun) =
          (C.target e.val).map (Replacement.host C hole K)
        simp only [List.map_map]
        congr 1; funext v; exact RelIsoPlug.map_host C hole f v
    | inr e =>
        change ((H.target e).map (Replacement.insert C hole H)).map
          (Port.map (RelIsoPlug.vertices C hole f).toFun) =
          (K.target (f.edges.toFun e)).map (Replacement.insert C hole K)
        calc
          _ = ((H.target e).map (Port.map f.vertices.toFun)).map (Replacement.insert C hole K) := by
            simp only [List.map_map]
            congr 1; funext v; exact RelIsoPlug.map_insert C hole f v
          _ = _ := by rw [f.target]

end Hypernets.Graph.Net
