import Hypernets.Copying.TranslatedComposition

/-! Resource permutations of the literal use-major distributor forest. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Distributor
open Graph

/-- Permute resource tags while leaving every use index unchanged. -/
def resourceTags {k : Nat} (π : Bijection (Fin k) (Fin k)) (X : Type) :
    Bijection (Σ _ : Fin k, X) (Σ _ : Fin k, X) where
  toFun p := ⟨π.toFun p.1,p.2⟩
  invFun p := ⟨π.invFun p.1,p.2⟩
  left_inv p := by rcases p with ⟨i,x⟩; simp [π.left_inv]
  right_inv p := by rcases p with ⟨i,x⟩; simp [π.right_inv]

/-- Apply the same resource permutation at every use and at the output. -/
def permutedBoundary (s : ShareSort) {k : Nat} (m : Nat)
    (π : Bijection (Fin k) (Fin k)) :
    Net.Parallel.Boundary (fun _ : Fin k => List.replicate m s.wire) (fun _ => [s.wire])
      (List.replicate (k*m) s.wire) (List.replicate k s.wire) where
  inputs := (resourceTags π _).trans (boundary s k m).inputs
  outputs := (resourceTags π _).trans (boundary s k m).outputs
  input_label i j := (boundary s k m).input_label (π.toFun i) j
  output_label i j := (boundary s k m).output_label (π.toFun i) j

/-- The input order remains use-major: only i changes to π(i). -/
theorem permuted_input_position (s : ShareSort) {k m}
    (π : Bijection (Fin k) (Fin k)) (i : Fin k)
    (j : Fin (List.replicate m s.wire).length) :
    ((permutedBoundary s m π).inputs.toFun ⟨i,j⟩).val = (π.toFun i).val+k*j.val := rfl

theorem permuted_output_position (s : ShareSort) {k m}
    (π : Bijection (Fin k) (Fin k)) (i : Fin k) :
    ((permutedBoundary s m π).outputs.toFun ⟨i,0⟩).val = (π.toFun i).val := rfl

/-- The same canonical trees with the explicitly permuted boundary attachment. -/
def permutedNet (s : ShareSort) {k : Nat} (m : Nat)
    (π : Bijection (Fin k) (Fin k)) :
    Net primitiveSignature (List.replicate (k*m) s.wire) (List.replicate k s.wire) :=
  Net.Parallel.net (fun _ : Fin k => CanonicalTree.net s m)
    (permutedBoundary s m π) (Enumeration.fin k)

/-- Component retagging preserves the actual boundary ports, not just their types. -/
theorem permuted_embed (s : ShareSort) {k : Nat} (m : Nat)
    (π : Bijection (Fin k) (Fin k)) (i : Fin k) (v : (CanonicalTree.net s m).Vertex) :
    Port.map (resourceTags π (CanonicalTree.net s m).Internal).toFun
      (Net.Parallel.embed (fun _ : Fin k => CanonicalTree.net s m) (permutedBoundary s m π) i v) =
    Net.Parallel.embed (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) (π.toFun i) v := by
  cases v <;> rfl

/-- Resource permutation only renames the forest's component carriers; all
canonical weakening and contraction edges, and ordered incidences, remain. -/
def permuted_iso (s : ShareSort) {k : Nat} (m : Nat)
    (π : Bijection (Fin k) (Fin k)) : Net.Iso (permutedNet s m π) (net s k m) where
  vertices := resourceTags π _
  edges := resourceTags π _
  internal_label _ := rfl
  edge_label _ := rfl
  source e := by
    rcases e with ⟨i,e⟩
    change (((CanonicalTree.net s m).source e).map _).map _ = ((CanonicalTree.net s m).source e).map _
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => permuted_embed s m π i v)
  target e := by
    rcases e with ⟨i,e⟩
    change (((CanonicalTree.net s m).target e).map _).map _ = ((CanonicalTree.net s m).target e).map _
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => permuted_embed s m π i v)

/-- The boundary-permuted forest at an arbitrary original box allowance. -/
def permutedAtDepth (s : ShareSort) {k : Nat} (m d : Nat)
    (π : Bijection (Fin k) (Fin k)) :
    Hypernet d (List.replicate (k*m) s.wire) (List.replicate k s.wire) :=
  (permutedNet s m π).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)

def permuted_deepIso (s : ShareSort) {k : Nat} (m d : Nat)
    (π : Bijection (Fin k) (Fin k)) :
    DeepIso (permutedAtDepth s m d π) (atDepth s k m d) where
  vertices := (permuted_iso s m π).vertices
  edges := (permuted_iso s m π).edges
  internal_label := (permuted_iso s m π).internal_label
  edge_label _ := labelEquiv_refl d _
  source := (permuted_iso s m π).source
  target := (permuted_iso s m π).target

end Hypernets.Copying.Distributor

namespace Hypernets.Copying.Translation
open Graph

/-- Independent resource permutations in the term and atom forests; the two
wire sorts and the original variable-before-atom ordering never mix. -/
def permutedEnvironmentDistributor (d k h m : Nat)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Hypernet d (environmentInterface (k*m) (h*m)) (environmentInterface k h) :=
  Net.Tensor.net (Distributor.permutedAtDepth .term m d ρ)
    (Distributor.permutedAtDepth .atom m d α)

/-- The literal combined distributor is equivariant under resource permutations. -/
def environmentDistributor_permutation (d k h m : Nat)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    DeepIso (permutedEnvironmentDistributor d k h m ρ α) (environmentDistributor d k h m) :=
  ParallelPair.congr (Net.Tensor.boundary _ _ _ _)
    (Distributor.permuted_deepIso .term m d ρ) (Distributor.permuted_deepIso .atom m d α)

/-- Single-use distributors are retained, including their weakening edges. -/
def singleUse_permutation (d k h : Nat)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    DeepIso (castInterfaces (by simp) rfl (permutedEnvironmentDistributor d k h 1 ρ α))
      (singleUse d k h) :=
  castInterfaces_congr _ _ (environmentDistributor_permutation d k h 1 ρ α)
end Hypernets.Copying.Translation
