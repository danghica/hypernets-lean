import Hypernets.Copying.SelectedResourceRenaming

/-! Typed boundary renaming through the literal ordered parallel assembly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryParallel
open Graph
variable {d : Nat} {A : Type} {I O J K : A → List Wire}
    {G : ∀ a, Hypernet d (I a) (O a)} {H : ∀ a, Hypernet d (J a) (K a)}
    (f : ∀ a, BoundaryIso (G a) (H a))

def componentPorts : Bijection (Σ a, (G a).Vertex) (Σ a, (H a).Vertex) where
  toFun x := ⟨x.1,(f x.1).ports.toFun x.2⟩
  invFun x := ⟨x.1,(f x.1).ports.invFun x.2⟩
  left_inv x := by rcases x with ⟨a,v⟩; simp [(f a).ports.left_inv]
  right_inv x := by rcases x with ⟨a,v⟩; simp [(f a).ports.right_inv]

def componentEdges : Bijection (Σ a, (G a).Edge) (Σ a, (H a).Edge) where
  toFun x := ⟨x.1,(f x.1).edges.toFun x.2⟩
  invFun x := ⟨x.1,(f x.1).edges.invFun x.2⟩
  left_inv x := by rcases x with ⟨a,v⟩; simp [(f a).edges.left_inv]
  right_inv x := by rcases x with ⟨a,v⟩; simp [(f a).edges.right_inv]

variable {U V W X : List Wire}
    (B : Net.Parallel.Boundary I O U V) (C : Net.Parallel.Boundary J K W X)

def ports : Bijection (Net.Parallel.Vertex G (J := U) (K := V))
    (Net.Parallel.Vertex H (J := W) (K := X)) :=
  (Net.Parallel.vertices G B).symm.trans ((componentPorts f).trans (Net.Parallel.vertices H C))

theorem embed (a : A) (v : (G a).Vertex) :
    (ports f B C).toFun (Net.Parallel.embed G B a v) =
      Net.Parallel.embed H C a ((f a).ports.toFun v) := by
  change (Net.Parallel.vertices H C).toFun ((componentPorts f).toFun
    ((Net.Parallel.vertices G B).invFun ((Net.Parallel.vertices G B).toFun ⟨a,v⟩))) = _
  rw [Bijection.left_inv]; rfl

/-- Assembly preserves wire typing, boundary roles, and the order of every incidence list. -/
def iso (finite : Enumeration A) :
    BoundaryIso (Net.Parallel.net G B finite) (Net.Parallel.net H C finite) where
  ports := ports f B C
  edges := componentEdges f
  vertex_label v := by
    have hv := (Net.Parallel.vertices G B).right_inv v
    generalize hx : (Net.Parallel.vertices G B).invFun v = x at hv
    obtain ⟨a,w⟩ := x
    change Net.Parallel.embed G B a w = v at hv
    subst v
    rw [embed]
    exact (Net.Parallel.embed_label H C a _).trans
      ((f a).vertex_label w |>.trans (Net.Parallel.embed_label G B a w).symm)
  input_iff v := by
    have hv := (Net.Parallel.vertices G B).right_inv v
    generalize hx : (Net.Parallel.vertices G B).invFun v = x at hv
    obtain ⟨a,w⟩ := x
    change Net.Parallel.embed G B a w = v at hv
    subst v
    rw [embed,Net.Parallel.embed_isInput,Net.Parallel.embed_isInput]
    exact (f a).input_iff w
  output_iff v := by
    have hv := (Net.Parallel.vertices G B).right_inv v
    generalize hx : (Net.Parallel.vertices G B).invFun v = x at hv
    obtain ⟨a,w⟩ := x
    change Net.Parallel.embed G B a w = v at hv
    subst v
    rw [embed,Net.Parallel.embed_isOutput,Net.Parallel.embed_isOutput]
    exact (f a).output_iff w
  edge_label e := (f e.1).edge_label e.2
  source e := by
    rcases e with ⟨a,e⟩
    change (((G a).source e).map _).map _ = ((H a).source ((f a).edges.toFun e)).map _
    rw [← (f a).source e]
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => embed f B C a v)
  target e := by
    rcases e with ⟨a,e⟩
    change (((G a).target e).map _).map _ = ((H a).target ((f a).edges.toFun e)).map _
    rw [← (f a).target e]
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => embed f B C a v)
end Hypernets.Copying.BoundaryParallel

namespace Hypernets.Copying.BoundaryIso
open Graph
/-- Ordered tensor assembly transports the two boundary actions independently. -/
def tensor {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    {G' : Hypernet d U V} {H' : Hypernet d W X} (f : BoundaryIso G G') (g : BoundaryIso H H') :
    BoundaryIso (Net.Tensor.net G H) (Net.Tensor.net G' H') :=
  BoundaryParallel.iso (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary _ _ _ _) (Net.Tensor.boundary _ _ _ _)
    ⟨[false,true],by intro b; cases b <;> simp⟩
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.Translation
open Graph
/-- The original variable graph follows a bijective change of variable and atom resources. -/
def variableTerm_rename (d : Nat) {k h}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (i : Fin k) :
    BoundaryIso (variableTerm d h i) (variableTerm d h (ρ.toFun i)) := by
  unfold variableTerm
  exact BoundaryIso.castInterfaces _ _ _ _
    ((selectedResource_rename d .term ρ i).tensor (Distributor.boundaryIso .atom 0 d α))

/-- Constants retain and correctly permute all ambient weakening resources. -/
def constant_rename (d : Nat) {k h}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (c : Constant) :
    BoundaryIso (constant d k h c) (constant d k h c) := by
  unfold constant
  exact BoundaryIso.castInterfaces _ _ _ _
    (((Distributor.boundaryIso .term 0 d ρ).tensor (BoundaryIso.refl _)).tensor
      (Distributor.boundaryIso .atom 0 d α))
end Hypernets.Copying.Translation
