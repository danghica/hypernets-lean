import Hypernets.Copying.CanonicalTree
import Hypernets.Graph.Parallel
import Hypernets.Graph.FinGrid
import Hypernets.Graph.PathRank
import Hypernets.Copying.Predicates

/-! Definition 10.1: D_{k,m} is a forest of k canonical trees, with
input (use j, resource i) at position i+k*j, and output i at position i. -/
namespace Hypernets.Copying
open Graph
namespace Distributor

/-- Scatter one canonical tree's inputs into the use-major distributor interface. -/
def inputIndex (s : ShareSort) {k m}
    (p : Σ _ : Fin k, Fin (List.replicate m s.wire).length) :
    Fin (List.replicate (k*m) s.wire).length :=
  let n := FinGrid.index p.1 ⟨p.2.val,by simpa using p.2.isLt⟩
  ⟨n.val,by simpa using n.isLt⟩

def inputSplit (s : ShareSort) {k m} (n : Fin (List.replicate (k*m) s.wire).length) :
    Σ _ : Fin k, Fin (List.replicate m s.wire).length :=
  let p := FinGrid.split (⟨n.val,by simpa using n.isLt⟩ : Fin (k*m))
  ⟨p.1,⟨p.2.val,by simpa using p.2.isLt⟩⟩

theorem inputSplit_index (s : ShareSort) {k m}
    (p : Σ _ : Fin k, Fin (List.replicate m s.wire).length) :
    inputSplit s (inputIndex s p) = p := by
  obtain ⟨i,j⟩ := p
  apply Sigma.ext
  · apply Fin.ext
    simp [inputSplit, inputIndex, FinGrid.split, FinGrid.index, Nat.mod_eq_of_lt i.isLt]
  · apply heq_of_eq
    apply Fin.ext
    simp [inputSplit, inputIndex, FinGrid.split, FinGrid.index,
      Nat.add_mul_div_left i.val j.val (show 0 < k by have h := i.isLt; omega), Nat.div_eq_of_lt i.isLt]

theorem inputIndex_split (s : ShareSort) {k m} (n : Fin (List.replicate (k*m) s.wire).length) :
    inputIndex s (inputSplit s n) = n := by
  apply Fin.ext
  exact Nat.mod_add_div _ _

/-- The boundary bijections implement the ordered input permutation, not just counts. -/
def boundary (s : ShareSort) (k m : Nat) :
    Net.Parallel.Boundary (fun _ : Fin k => List.replicate m s.wire) (fun _ => [s.wire])
      (List.replicate (k*m) s.wire) (List.replicate k s.wire) where
  inputs := ⟨inputIndex s,inputSplit s,inputSplit_index s,inputIndex_split s⟩
  outputs := {
    toFun p := ⟨p.1.val,by simpa using p.1.isLt⟩
    invFun i := ⟨⟨i.val,by simpa using i.isLt⟩,0⟩
    left_inv p := by
      obtain ⟨i,j⟩ := p
      have z : j = 0 := Fin.ext (by change j.val = 0; have := j.isLt; change j.val < 1 at this; omega)
      subst j
      rfl
    right_inv _ := rfl
  }
  input_label _ _ := by simp
  output_label _ _ := by simp

/-- The actual finite graph D_{k,m}, including empty forests and pure weakening. -/
@[reducible] def net (s : ShareSort) (k m : Nat) :
    Net primitiveSignature (List.replicate (k*m) s.wire) (List.replicate k s.wire) :=
  Net.Parallel.net (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) (Enumeration.fin k)

/-- The exact input permutation: tree i, leaf j occupies position i+k*j. -/
theorem input_position (s : ShareSort) {k m} (i : Fin k)
    (j : Fin (List.replicate m s.wire).length) :
    ((boundary s k m).inputs.toFun ⟨i,j⟩).val = i.val+k*j.val := rfl

theorem output_position (s : ShareSort) {k m} (i : Fin k) :
    ((boundary s k m).outputs.toFun ⟨i,0⟩).val = i.val := rfl

/-- Each component has exactly its canonical weakening, with no shared internal nodes. -/
theorem weakening_iff (s : ShareSort) (k m : Nat) (i : Fin k) (e : Fin (m+1)) :
    (net s k m).edgeLabel ⟨i,e⟩ = .weakening s ↔ e = 0 :=
  CanonicalTree.weakening_iff s m e

theorem contraction_iff (s : ShareSort) (k m : Nat) (i : Fin k) (e : Fin (m+1)) :
    (net s k m).edgeLabel ⟨i,e⟩ = .contraction s ↔ e ≠ 0 :=
  CanonicalTree.contraction_iff s m e

/-- Typed distributors are available at every finite box allowance. -/
def atDepth (s : ShareSort) (k m d : Nat) :
    Hypernet d (List.replicate (k*m) s.wire) (List.replicate k s.wire) :=
  (net s k m).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)

/-- The forest has no adjacency between distinct resources. -/
theorem adjacent_tag (s : ShareSort) (k m : Nat) {i j : Fin k} {e f : Fin (m+1)}
    (h : (net s k m).Adjacent ⟨i,e⟩ ⟨j,f⟩) : i = j :=
  Net.Parallel.adjacent_tag _ _ _ h

theorem adjacent_same (s : ShareSort) (k m : Nat) (i : Fin k) (e f : Fin (m+1)) :
    (net s k m).Adjacent ⟨i,e⟩ ⟨i,f⟩ ↔ (CanonicalTree.net s m).Adjacent e f :=
  Net.Parallel.adjacent_same (fun _ : Fin k => CanonicalTree.net s m) (boundary s k m) (Enumeration.fin k) i e f

/-- Canonical-tree rank remains strictly increasing after input interleaving. -/
theorem adjacent_rank_lt (s : ShareSort) (k m : Nat)
    {e f : (net s k m).Edge} (h : (net s k m).Adjacent e f) :
    CanonicalTree.rank e.2 < CanonicalTree.rank f.2 := by
  obtain ⟨i,e⟩ := e
  obtain ⟨j,f⟩ := f
  have tags := adjacent_tag s k m h
  subst j
  exact CanonicalTree.adjacent_rank_lt s m ((adjacent_same s k m i e f).mp h)

/-- Distributors cannot introduce cyclic paths even when some interfaces are empty. -/
theorem path_nodup (s : ShareSort) (k m : Nat) {es : List (net s k m).Edge}
    (path : (net s k m).Path es) : es.Nodup :=
  Net.path_nodup_of_rank (net s k m) (fun e => CanonicalTree.rank e.2)
    (adjacent_rank_lt s k m) path

/-- The case k=0 has no edges or internal vertices. -/
theorem zero_edges (s : ShareSort) (m : Nat) (e : (net s 0 m).Edge) : False := Fin.elim0 e.1

theorem zero_internal (s : ShareSort) (m : Nat) (v : (net s 0 m).Internal) : False := Fin.elim0 v.1

/-- The case m=0 consists entirely of weakenings; it is not empty when k>0. -/
theorem zero_uses (s : ShareSort) (k : Nat) (e : (net s k 0).Edge) :
    (net s k 0).edgeLabel e = .weakening s := by
  apply (weakening_iff s k 0 e.1 e.2).mpr
  apply Fin.ext
  change e.2.val = 0
  have := e.2.isLt
  omega

/-- No label other than a weakening or contraction is introduced by a distributor. -/
theorem allLabels_atDepth (P : Primitive → Prop) (s : ShareSort) (k m d : Nat)
    (weak : P (.weakening s)) (contract : P (.contraction s)) :
    AllLabels P (atDepth s k m d) := by
  intro e
  cases d <;> change P (CanonicalTree.label s e.2)
  all_goals unfold CanonicalTree.label; split <;> assumption

theorem focusFree (s : ShareSort) (k m d : Nat) : FocusFree (atDepth s k m d) :=
  allLabels_atDepth _ s k m d (by intro mode h; cases h) (by intro mode h; cases h)

theorem holeFree (s : ShareSort) (k m d : Nat) : HoleFree (atDepth s k m d) :=
  allLabels_atDepth _ s k m d (by intro hole h; cases h) (by intro hole h; cases h)

end Distributor
end Hypernets.Copying
