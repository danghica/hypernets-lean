import Hypernets.Copying.BoundaryIso

/-! Distributor equivariance stated directly on the original graph, with
explicit resource permutations on its external boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Distributor
open Graph

def resourcePorts (s : ShareSort) {k : Nat} (m : Nat)
    (π : Bijection (Fin k) (Fin k)) : Bijection (net s k m).Vertex (net s k m).Vertex :=
  (Net.Parallel.vertices (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m)).symm.trans
    ((resourceTags π _).trans
      (Net.Parallel.vertices (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m)))

theorem resourcePorts_embed (s : ShareSort) {k : Nat} (m : Nat)
    (π : Bijection (Fin k) (Fin k)) (i : Fin k) (v : (CanonicalTree.net s m).Vertex) :
    (resourcePorts s m π).toFun
      (Net.Parallel.embed (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) i v) =
    Net.Parallel.embed (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) (π.toFun i) v := by
  change (Net.Parallel.vertices _ _).toFun ((resourceTags π _).toFun
    ((Net.Parallel.vertices _ _).invFun ((Net.Parallel.vertices _ _).toFun ⟨i,v⟩))) = _
  rw [Bijection.left_inv]
  rfl

/-- Each use's external input carries the same resource permutation. -/
theorem resourcePorts_input (s : ShareSort) {k m}
    (π : Bijection (Fin k) (Fin k)) (i : Fin k)
    (j : Fin (List.replicate m s.wire).length) :
    (resourcePorts s m π).toFun (.input (inputIndex s ⟨i,j⟩)) =
      .input (inputIndex s ⟨π.toFun i,j⟩) :=
  resourcePorts_embed s m π i (.input j)

theorem resourcePorts_output (s : ShareSort) {k m}
    (π : Bijection (Fin k) (Fin k)) (i : Fin k) :
    (resourcePorts s m π).toFun (.output ⟨i.val,by simp⟩) =
      .output ⟨(π.toFun i).val,by simp⟩ :=
  resourcePorts_embed s m π i (.output 0)

/-- A boundary-permuting automorphism of the unchanged distributor at every
allowance. The external positions move exactly as the preceding two laws state. -/
def boundaryIso (s : ShareSort) {k : Nat} (m d : Nat)
    (π : Bijection (Fin k) (Fin k)) : BoundaryIso (atDepth s k m d) (atDepth s k m d) where
  ports := resourcePorts s m π
  edges := resourceTags π _
  vertex_label v := by
    let B := Net.Parallel.vertices (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m)
    have hv := B.right_inv v
    generalize hx : B.invFun v = x at hv
    obtain ⟨i,w⟩ := x
    change Net.Parallel.embed _ (boundary s k m) i w = v at hv
    subst v
    rw [resourcePorts_embed]
    exact (Net.Parallel.embed_label (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) (π.toFun i) w).trans
      (Net.Parallel.embed_label (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) i w).symm
  input_iff v := by
    let B := Net.Parallel.vertices (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m)
    have hv := B.right_inv v
    generalize hx : B.invFun v = x at hv
    obtain ⟨i,w⟩ := x
    change Net.Parallel.embed _ (boundary s k m) i w = v at hv
    subst v
    rw [resourcePorts_embed]
    cases w <;> rfl
  output_iff v := by
    let B := Net.Parallel.vertices (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m)
    have hv := B.right_inv v
    generalize hx : B.invFun v = x at hv
    obtain ⟨i,w⟩ := x
    change Net.Parallel.embed _ (boundary s k m) i w = v at hv
    subst v
    rw [resourcePorts_embed]
    cases w <;> rfl
  edge_label _ := labelEquiv_refl _ _
  source e := by
    rcases e with ⟨i,e⟩
    change (((CanonicalTree.net s m).source e).map _).map _ = ((CanonicalTree.net s m).source e).map _
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => resourcePorts_embed s m π i v)
  target e := by
    rcases e with ⟨i,e⟩
    change (((CanonicalTree.net s m).target e).map _).map _ = ((CanonicalTree.net s m).target e).map _
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => resourcePorts_embed s m π i v)
end Hypernets.Copying.Distributor
