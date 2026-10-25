import Hypernets.Graph.Parallel
import Hypernets.Graph.RelIso

/-! Ordered parallel assembly preserves component-wise label-related isomorphisms. -/
namespace Hypernets.Graph.Net.ParallelIso
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {X : Type}
    {I O : X → List L} {R : Op → Op → Prop}
    {F H : (a : X) → Net σ (I a) (O a)} (f : ∀ a, RelIso R (F a) (H a))

/-- Rename each internal vertex within its original component. -/
def vertices : Bijection (Σ a, (F a).Internal) (Σ a, (H a).Internal) where
  toFun x := ⟨x.1,(f x.1).vertices.toFun x.2⟩
  invFun x := ⟨x.1,(f x.1).vertices.invFun x.2⟩
  left_inv x := by rcases x with ⟨a,x⟩; simp [(f a).vertices.left_inv]
  right_inv x := by rcases x with ⟨a,x⟩; simp [(f a).vertices.right_inv]

/-- Rename each edge within its original component. -/
def edges : Bijection (Σ a, (F a).Edge) (Σ a, (H a).Edge) where
  toFun x := ⟨x.1,(f x.1).edges.toFun x.2⟩
  invFun x := ⟨x.1,(f x.1).edges.invFun x.2⟩
  left_inv x := by rcases x with ⟨a,x⟩; simp [(f a).edges.left_inv]
  right_inv x := by rcases x with ⟨a,x⟩; simp [(f a).edges.right_inv]

/-- The chosen boundary permutation commutes with every component renaming. -/
theorem map_embed {J K} (B : Parallel.Boundary I O J K) (a : X) (v : (F a).Vertex) :
    Port.map (vertices f).toFun (Parallel.embed F B a v) =
      Parallel.embed H B a (Port.map (f a).vertices.toFun v) := by cases v <;> rfl

/-- Assemble the component isomorphisms without changing any boundary ordering. -/
def iso {J K} (B : Parallel.Boundary I O J K) (finite : Enumeration X) :
    RelIso R (Parallel.net F B finite) (Parallel.net H B finite) where
  vertices := vertices f
  edges := edges f
  internal_label x := (f x.1).internal_label x.2
  edge_label x := (f x.1).edge_label x.2
  source x := by
    rcases x with ⟨a,x⟩
    change (((F a).source x).map _).map _ = ((H a).source ((f a).edges.toFun x)).map _
    rw [← (f a).source x]
    simp only [edges,List.map_map]
    exact List.map_congr_left (fun v _ => map_embed f B a v)
  target x := by
    rcases x with ⟨a,x⟩
    change (((F a).target x).map _).map _ = ((H a).target ((f a).edges.toFun x)).map _
    rw [← (f a).target x]
    simp only [edges,List.map_map]
    exact List.map_congr_left (fun v _ => map_embed f B a v)
end Hypernets.Graph.Net.ParallelIso
