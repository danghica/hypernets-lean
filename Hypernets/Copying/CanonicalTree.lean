import Hypernets.Copying.Hierarchy

/-! Definition 10.1: the ordered canonical tree D_{1,m}. Edge zero is the
weakening. For m>0 edge one is the root contraction; its left child is the
weakening, and the right spine successively merges the ordered inputs. -/
namespace Hypernets.Copying
open Graph
namespace CanonicalTree

abbrev Vertex (s : ShareSort) (m : Nat) :=
  Port (Fin m) (List.replicate m s.wire).length 1

/-- The output of the weakening or a contraction; edge one is the root. -/
def node {s : ShareSort} {m} (e : Fin (m+1)) : Vertex s m :=
  if z : m = 0 then .output 0 else
  if w : e.val = 0 then .internal ⟨0,by omega⟩ else
  if r : e.val = 1 then .output 0 else .internal ⟨e.val-1,by omega⟩

/-- Sources follow the left-to-right ordering in Definition 10.1. -/
def sources {s : ShareSort} {m} (e : Fin (m+1)) : List (Vertex s m) :=
  if h : e.val = 0 then [] else
    [if e.val = 1 then .internal ⟨0,by omega⟩ else .input ⟨e.val-2,by simp; omega⟩,
     if b : e.val < m then .internal ⟨e.val,b⟩ else .input ⟨m-1,by simp; omega⟩]

def label (s : ShareSort) {m} (e : Fin (m+1)) : Primitive :=
  if e.val = 0 then .weakening s else .contraction s

theorem node_injective {s : ShareSort} {m} {e f : Fin (m+1)}
    (h : node (s := s) e = node f) : e = f := by
  unfold node at h
  split at h
  · apply Fin.ext; omega
  · (repeat' split at h) <;>
      simp_all <;> apply Fin.ext <;> omega

theorem node_not_input {s : ShareSort} {m} (e : Fin (m+1)) :
    ¬ (node (s := s) e).IsInput := by
  unfold node
  split <;> (try split) <;> (try split) <;> simp [Port.IsInput]

theorem sources_nodup {s : ShareSort} {m} (e : Fin (m+1)) :
    (sources (s := s) e).Nodup := by
  unfold sources
  split
  · simp
  · split <;> split <;> simp_all <;> omega

theorem source_unique {s : ShareSort} {m} {v : Vertex s m} {e f : Fin (m+1)}
    (he : v ∈ sources e) (hf : v ∈ sources f) : e = f := by
  unfold sources at he hf
  split at he
  · simp_all
  split at hf
  · simp_all
  split at he <;> split at he <;> split at hf <;> split at hf
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at he hf
  all_goals rcases he with rfl | rfl
  all_goals rcases hf with hf | hf
  all_goals simp only [Port.input.injEq, Port.internal.injEq, reduceCtorEq, Fin.mk.injEq] at hf
  all_goals first | contradiction | (apply Fin.ext; omega)

theorem source_coverage {s : ShareSort} {m} (v : Vertex s m) :
    (∃ e, v ∈ sources e) ↔ ¬ v.IsOutput := by
  cases v with
  | internal i =>
    simp only [Port.IsOutput, not_false_eq_true, iff_true]
    by_cases z : i.val = 0
    · refine ⟨⟨1,by have := i.isLt; omega⟩,?_⟩
      simp only [sources, show (1 : Nat) ≠ 0 by decide, ↓reduceDIte, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      left
      exact congrArg Port.internal (Fin.ext z)
    · refine ⟨⟨i.val,by omega⟩,?_⟩
      simp [sources, z, i.isLt]
  | input i =>
    simp only [Port.IsOutput, not_false_eq_true, iff_true]
    have bound : i.val < m := by simpa using i.isLt
    by_cases last : i.val+1 = m
    · refine ⟨⟨m,by omega⟩,?_⟩
      simp [sources, show m ≠ 0 by omega]
      right
      apply Fin.ext
      simpa using (show i.val = m-1 by omega)
    · refine ⟨⟨i.val+2,by omega⟩,?_⟩
      simp [sources]
  | output i =>
    simp only [Port.IsOutput, not_true_eq_false, iff_false, not_exists]
    intro e
    unfold sources
    split <;> (try split) <;> (try split) <;> simp

theorem target_coverage {s : ShareSort} {m} (v : Vertex s m) :
    (∃ e, v = node e) ↔ ¬ v.IsInput := by
  constructor
  · rintro ⟨e,rfl⟩; exact node_not_input e
  · intro h
    cases v with
    | input i => exact False.elim (h trivial)
    | internal i =>
      by_cases z : i.val = 0
      · refine ⟨0,?_⟩
        simp [node, show m ≠ 0 by have := i.isLt; omega]
        exact Fin.ext z
      · refine ⟨⟨i.val+1,by omega⟩,?_⟩
        simp [node, show m ≠ 0 by have := i.isLt; omega, z]
    | output i =>
      have : i = 0 := Fin.ext (by omega)
      subst i
      by_cases z : m = 0
      · exact ⟨0,by simp [node, z]⟩
      · exact ⟨⟨1,by omega⟩,by simp [node, z]⟩

theorem vertex_label (s : ShareSort) {m} (v : Vertex s m) :
    Port.label (I := List.replicate m s.wire) (O := [s.wire])
      (fun _ : Fin m => s.wire) v = s.wire := by
  cases v <;> simp [Port.label]

/-- Explicit canonical tree, including all ordered-incidence and finiteness proofs. -/
@[reducible] def net (s : ShareSort) (m : Nat) : Net primitiveSignature (List.replicate m s.wire) [s.wire] where
  Internal := Fin m
  Edge := Fin (m+1)
  finiteInternal := Enumeration.fin m
  finiteEdge := Enumeration.fin (m+1)
  internalLabel _ := s.wire
  edgeLabel := label s
  source e := sources e
  target e := [node e]
  source_nodup := sources_nodup
  target_nodup _ := by simp
  source_unique := source_unique
  target_unique := by
    intro v e f he hf
    simp only [List.mem_singleton] at he hf
    exact node_injective (he.symm.trans hf)
  source_coverage := source_coverage
  target_coverage v := by simpa using target_coverage v
  source_typed e := by
    unfold sources label
    split <;> simp_all [primitiveSignature, vertex_label]
  target_typed e := by
    simp only [List.map_singleton, vertex_label]
    unfold label
    split <;> rfl

theorem weakening_iff (s : ShareSort) (m : Nat) (e : Fin (m+1)) :
    (net s m).edgeLabel e = .weakening s ↔ e = 0 := by
  change label s e = .weakening s ↔ e = 0
  have z : e = 0 ↔ e.val = 0 := Fin.ext_iff
  rw [z]
  unfold label
  split <;> simp_all

theorem contraction_iff (s : ShareSort) (m : Nat) (e : Fin (m+1)) :
    (net s m).edgeLabel e = .contraction s ↔ e ≠ 0 := by
  change label s e = .contraction s ↔ e ≠ 0
  have z : e = 0 ↔ e.val = 0 := Fin.ext_iff
  simp only [ne_eq, z]
  unfold label
  split <;> simp_all

/-- Adjacency runs from the weakening to the root, or upward along the right spine. -/
theorem adjacent_iff (s : ShareSort) (m : Nat) (e f : Fin (m+1)) :
    (net s m).Adjacent e f ↔
      (e.val = 0 ∧ f.val = 1) ∨ (1 < e.val ∧ f.val+1 = e.val) := by
  change (∃ v, v ∈ [node (s := s) e] ∧ v ∈ sources f) ↔ _
  simp only [List.mem_singleton, exists_eq_left]
  unfold node sources
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> simp_all <;> omega

/-- A topological rank; the weakening precedes the root and the spine ascends. -/
def rank {m} (e : Fin (m+1)) : Nat := if e.val = 0 then 0 else m+1-e.val

theorem adjacent_rank_lt (s : ShareSort) (m : Nat) {e f : Fin (m+1)}
    (h : (net s m).Adjacent e f) : rank e < rank f := by
  have h := (adjacent_iff s m e f).mp h
  unfold rank
  split <;> split <;> omega

/-- Every nontrivial path progresses strictly in rank. -/
theorem path_rank_lt (s : ShareSort) (m : Nat) {es : List (Fin (m+1))}
    (path : (net s m).Path es) {i j : Nat} (hi : i < es.length) (hj : j < es.length)
    (ij : i < j) : rank es[i] < rank es[j] := by
  induction es generalizing i j with
  | nil => simp at hi
  | cons e es ih =>
    cases es with
    | nil => simp at hi hj; omega
    | cons f es =>
      obtain ⟨adj,tailPath⟩ := Net.path_pair_iff.mp path
      have step := adjacent_rank_lt s m adj
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j =>
          cases j with
          | zero => exact step
          | succ j =>
            have tail := ih tailPath (i := 0) (j := j+1) (by simp) (by simpa using hj) (by omega)
            exact Nat.lt_trans step tail
      | succ i =>
        cases j with
        | zero => omega
        | succ j => exact ih tailPath (by simpa using hi) (by simpa using hj) (by omega)

/-- A path cannot revisit an edge; no acyclicity axiom was added to general graphs. -/
theorem path_nodup (s : ShareSort) (m : Nat) {es : List (Fin (m+1))}
    (path : (net s m).Path es) : es.Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  by_cases ne : i = j
  · exact ne
  apply False.elim
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · have h := path_rank_lt s m path hi hj lt
    rw [eq] at h
    exact Nat.lt_irrefl _ h
  · have h := path_rank_lt s m path hj hi gt
    rw [eq] at h
    exact Nat.lt_irrefl _ h

/-- Realize the canonical graph in any finite copying alphabet. -/
def atDepth (s : ShareSort) (m d : Nat) : Hypernet d (List.replicate m s.wire) [s.wire] :=
  (net s m).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)

end CanonicalTree
end Hypernets.Copying
