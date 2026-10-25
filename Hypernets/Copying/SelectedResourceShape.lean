import Hypernets.Copying.DistributorBoundaryIso

/-! Explicit carrier coordinates for the unchanged selected-resource clause. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SelectedResource
open Graph

/-- Exactly the tensor expression inside Figure 16's selected-resource clause. -/
def raw (s : ShareSort) (d : Nat) {n} (i : Fin n) :=
  Net.Tensor.net (Net.Tensor.net (Distributor.atDepth s i.val 0 d)
    (Distributor.atDepth s 1 1 d)) (Distributor.atDepth s (n-i.val-1) 0 d)

def edgeIndex (s : ShareSort) (d : Nat) {n} (i : Fin n) : (raw s d i).Edge → Fin n ⊕ Unit
  | ⟨false,⟨false,⟨j,_⟩⟩⟩ => .inl ⟨j.val,by have := j.isLt; have := i.isLt; omega⟩
  | ⟨false,⟨true,⟨_,e⟩⟩⟩ => if e.val = 0 then .inl i else .inr ()
  | ⟨true,⟨j,_⟩⟩ => .inl ⟨i.val+1+j.val,by have := j.isLt; have := i.isLt; omega⟩

def edgeAt (s : ShareSort) (d : Nat) {n} (i : Fin n) : Fin n ⊕ Unit → (raw s d i).Edge
  | .inl j => if h : j.val < i.val then ⟨false,⟨false,⟨⟨j.val,h⟩,0⟩⟩⟩
    else if eq : j.val = i.val then ⟨false,⟨true,⟨0,0⟩⟩⟩
    else ⟨true,⟨⟨j.val-i.val-1,by have := j.isLt; have := i.isLt; omega⟩,0⟩⟩
  | .inr _ => ⟨false,⟨true,⟨0,1⟩⟩⟩

theorem edgeIndex_at (s : ShareSort) (d : Nat) {n} (i : Fin n) (x : Fin n ⊕ Unit) :
    edgeIndex s d i (edgeAt s d i x) = x := by
  cases x with
  | inr x => cases x; rfl
  | inl j =>
    simp only [edgeAt]
    split
    · rfl
    · split
      · rename_i h eq; change Sum.inl i = Sum.inl j; exact congrArg Sum.inl (Fin.ext eq.symm)
      · simp only [edgeIndex]; congr 1; apply Fin.ext; simp; omega

theorem edgeAt_index (s : ShareSort) (d : Nat) {n} (i : Fin n) (e : (raw s d i).Edge) :
    edgeAt s d i (edgeIndex s d i e) = e := by
  rcases e with ⟨a,e⟩
  cases a with
  | false =>
    rcases e with ⟨b,e⟩
    cases b with
    | false =>
      rcases e with ⟨j,e⟩
      have he : e = 0 := Fin.ext (by have := e.isLt; change e.val < 1 at this; omega)
      subst e
      simp [edgeIndex,edgeAt,j.isLt]
    | true =>
      rcases e with ⟨j,e⟩
      have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
      subst j
      have he : e = 0 ∨ e = 1 := by
        by_cases h : e.val = 0
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext (by change e.val = 1; have := e.isLt; change e.val < 2 at this; omega))
      rcases he with rfl | rfl <;> simp [edgeIndex,edgeAt]
  | true =>
    rcases e with ⟨j,e⟩
    have he : e = 0 := Fin.ext (by have := e.isLt; change e.val < 1 at this; omega)
    subst e
    simp [edgeIndex,edgeAt,show ¬ i.val+1+j.val < i.val by omega,
      show ¬ i.val+1+j.val = i.val by omega,show i.val+1+j.val-i.val-1 = j.val by omega]

def edges (s : ShareSort) (d : Nat) {n} (i : Fin n) : Bijection (raw s d i).Edge (Fin n ⊕ Unit) :=
  ⟨edgeIndex s d i,edgeAt s d i,edgeAt_index s d i,edgeIndex_at s d i⟩


def internal (s : ShareSort) (d : Nat) {n} (i : Fin n) : Bijection (raw s d i).Internal Unit where
  toFun _ := ()
  invFun _ := ⟨false,⟨true,⟨0,0⟩⟩⟩
  left_inv v := by
    rcases v with ⟨a,v⟩
    cases a with
    | false =>
      rcases v with ⟨b,v⟩
      cases b with
      | false => exact Fin.elim0 v.2
      | true =>
        rcases v with ⟨j,v⟩
        have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
        have hv : v = 0 := Fin.ext (by have := v.isLt; change v.val < 1 at this; omega)
        subst j; subst v; rfl
    | true => exact Fin.elim0 v.2
  right_inv v := by cases v; rfl

theorem input_length (s : ShareSort) {n} (i : Fin n) :
    (((List.replicate (i.val*0) s.wire ++ List.replicate (1*1) s.wire) ++
      List.replicate ((n-i.val-1)*0) s.wire)).length = 1 := by simp

theorem output_length (s : ShareSort) {n} (i : Fin n) :
    ((List.replicate i.val s.wire ++ List.replicate 1 s.wire) ++
      List.replicate (n-i.val-1) s.wire).length = n := by
  simp only [List.length_append,List.length_replicate]
  have := i.isLt; omega

def ports (s : ShareSort) (d : Nat) {n} (i : Fin n) :
    Bijection (raw s d i).Vertex (Port Unit 1 n) where
  toFun
    | .internal v => .internal ((internal s d i).toFun v)
    | .input j => .input ⟨j.val,Nat.lt_of_lt_of_eq j.isLt (input_length s i)⟩
    | .output j => .output ⟨j.val,Nat.lt_of_lt_of_eq j.isLt (output_length s i)⟩
  invFun
    | .internal v => .internal ((internal s d i).invFun v)
    | .input j => .input ⟨j.val,by rw [input_length]; exact j.isLt⟩
    | .output j => .output ⟨j.val,by rw [output_length]; exact j.isLt⟩
  left_inv v := by cases v with
    | internal v => exact congrArg Port.internal ((internal s d i).left_inv v)
    | input j => rfl
    | output j => rfl
  right_inv v := by cases v with
    | internal v => exact congrArg Port.internal ((internal s d i).right_inv v)
    | input j => rfl
    | output j => rfl

/-- Canonical source and target lists are coordinates, not a replacement translation. -/
def source {n : Nat} : Fin n ⊕ Unit → List (Port Unit 1 n)
  | .inl _ => []
  | .inr _ => [.internal (),.input 0]

def target {n : Nat} (i : Fin n) : Fin n ⊕ Unit → List (Port Unit 1 n)
  | .inl j => [if j = i then .internal () else .output j]
  | .inr _ => [.output i]

def label (s : ShareSort) {n : Nat} : Fin n ⊕ Unit → Primitive
  | .inl _ => .weakening s
  | .inr _ => .contraction s



theorem source_at (s : ShareSort) (d : Nat) {n} (i : Fin n) (x : Fin n ⊕ Unit) :
    ((raw s d i).source (edgeAt s d i x)).map (ports s d i).toFun = source x := by
  cases x with
  | inl j =>
    simp only [edgeAt]
    split <;> try split
    all_goals rfl
  | inr x =>
    cases x
    simp [raw,edgeAt,source,ports,internal,Net.Tensor.net,Net.Tensor.family,
      Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,Net.Tensor.boundary,
      Net.Tensor.ports,Net.Tensor.join,Net.Tensor.interfaces,Distributor.atDepth,Distributor.net,
      Distributor.boundary,Distributor.inputIndex,FinGrid.index,CanonicalTree.net,
      CanonicalTree.sources,Net.relabel]

theorem target_at (s : ShareSort) (d : Nat) {n} (i : Fin n) (x : Fin n ⊕ Unit) :
    ((raw s d i).target (edgeAt s d i x)).map (ports s d i).toFun = target i x := by
  cases x with
  | inl j =>
    simp only [edgeAt]
    split <;> try split
    all_goals simp [raw,target,ports,internal,Net.Tensor.net,Net.Tensor.family,
      Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,Net.Tensor.boundary,
      Net.Tensor.ports,Net.Tensor.join,Net.Tensor.interfaces,Distributor.atDepth,Distributor.net,
      Distributor.boundary,CanonicalTree.net,CanonicalTree.node,Net.relabel]
    all_goals simp_all [Fin.ext_iff]
    all_goals omega
  | inr x =>
    cases x
    simp [raw,edgeAt,target,ports,internal,Net.Tensor.net,Net.Tensor.family,
      Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,Net.Tensor.boundary,
      Net.Tensor.ports,Net.Tensor.join,Net.Tensor.interfaces,Distributor.atDepth,Distributor.net,
      Distributor.boundary,CanonicalTree.net,CanonicalTree.node,Net.relabel]



theorem label_at (s : ShareSort) (d : Nat) {n} (i : Fin n) (x : Fin n ⊕ Unit) :
    (raw s d i).edgeLabel (edgeAt s d i x) = primitiveLabel d (label s x) := by
  cases x with
  | inl j =>
    simp only [edgeAt]
    split <;> (try split)
    all_goals cases d <;> rfl
  | inr x => cases x; cases d <;> rfl

theorem vertex_label (s : ShareSort) (d : Nat) {n} (i : Fin n) (v : (raw s d i).Vertex) :
    (raw s d i).vertexLabel v = s.wire := by
  cases v with
  | internal v =>
    have eq := (internal s d i).left_inv v
    change (⟨false,⟨true,⟨0,0⟩⟩⟩ : (raw s d i).Internal) = v at eq
    subst v
    rfl
  | input j =>
    have mem := List.getElem_mem (l := (List.replicate (i.val*0) s.wire ++ List.replicate (1*1) s.wire) ++
      List.replicate ((n-i.val-1)*0) s.wire) j.isLt
    simp only [List.mem_append,List.mem_replicate] at mem
    rcases mem with (mem | mem) | mem <;> exact mem.2
  | output j =>
    have mem := List.getElem_mem (l := (List.replicate i.val s.wire ++ List.replicate 1 s.wire) ++
      List.replicate (n-i.val-1) s.wire) j.isLt
    simp only [List.mem_append,List.mem_replicate] at mem
    rcases mem with (mem | mem) | mem <;> exact mem.2

end Hypernets.Copying.SelectedResource
