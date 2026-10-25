import Hypernets.Graph.Simultaneous
import Hypernets.Graph.RelIso

/-! Simultaneous expansion preserves component-wise recursive label isomorphisms. -/
namespace Hypernets.Graph.Net.ExpansionIso
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R : Op → Op → Prop} (C : Net σ I O)
    {F K : (b : C.Edge) → Net σ (σ.input (C.edgeLabel b)) (σ.output (C.edgeLabel b))}
    (f : ∀ b, RelIso R (F b) (K b))

/-- Apply each component's vertex renaming, retaining every skeleton vertex. -/
def vertices : Bijection (C.expand F).Internal (C.expand K).Internal where
  toFun
    | .inl v => .inl v
    | .inr ⟨b,v⟩ => .inr ⟨b,(f b).vertices.toFun v⟩
  invFun
    | .inl v => .inl v
    | .inr ⟨b,v⟩ => .inr ⟨b,(f b).vertices.invFun v⟩
  left_inv v := by rcases v with v | ⟨b,v⟩; rfl; simp [(f b).vertices.left_inv]
  right_inv v := by rcases v with v | ⟨b,v⟩; rfl; simp [(f b).vertices.right_inv]

/-- Component tags and their local edge bijections determine the expanded edge bijection. -/
def edges : Bijection (C.expand F).Edge (C.expand K).Edge where
  toFun x := ⟨x.1,(f x.1).edges.toFun x.2⟩
  invFun x := ⟨x.1,(f x.1).edges.invFun x.2⟩
  left_inv x := by rcases x with ⟨b,x⟩; simp [(f b).edges.left_inv]
  right_inv x := by rcases x with ⟨b,x⟩; simp [(f b).edges.right_inv]

theorem map_host (v : C.Vertex) :
    Port.map (vertices C f).toFun (Expansion.host C F v) = Expansion.host C K v := by
  cases v <;> rfl

theorem map_insert (b : C.Edge) (v : (F b).Vertex) :
    Port.map (vertices C f).toFun (Expansion.insert C F b v) =
      Expansion.insert C K b (Port.map (f b).vertices.toFun v) := by
  cases v with
  | internal v => rfl
  | input i => exact map_host C f _
  | output i => exact map_host C f _

/-- Component-wise label-related isomorphisms assemble to a label-related
isomorphism of the original expansions, with no new assumption on the pattern. -/
def iso : RelIso R (C.expand F) (C.expand K) where
  vertices := vertices C f
  edges := edges C f
  internal_label v := by
    rcases v with v | ⟨b,v⟩
    · rfl
    · exact (f b).internal_label v
  edge_label x := (f x.1).edge_label x.2
  source x := by
    rcases x with ⟨b,x⟩
    change (((F b).source x).map _).map _ = ((K b).source ((f b).edges.toFun x)).map _
    rw [← (f b).source x]
    simp only [edges,List.map_map]
    exact List.map_congr_left (fun v _ => map_insert C f b v)
  target x := by
    rcases x with ⟨b,x⟩
    change (((F b).target x).map _).map _ = ((K b).target ((f b).edges.toFun x)).map _
    rw [← (f b).target x]
    simp only [edges,List.map_map]
    exact List.map_congr_left (fun v _ => map_insert C f b v)
end Hypernets.Graph.Net.ExpansionIso
