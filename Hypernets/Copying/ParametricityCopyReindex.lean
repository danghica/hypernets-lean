import Hypernets.Copying.ParametricityFamilyIsolation

/-! Arbitrary injective selections and bijective reindexings of the literal
ordered copies. Every complete recursive member is preserved, and every
external coordinate follows the selected original member index. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyComponents
open Graph Opening
variable {d k : Nat} (G : Hypernet d [.term] (List.replicate k .term))

/-- A concrete injection of whole original copies, recording the complete
port and edge map of every member, including its nested box. -/
structure Selection {n m : Nat} (p : Fin n → Fin m) where
  occurrence : Occurrence (copies G n) (copies G m)
  member_ports : ∀ i v, occurrence.ports ((copy G n i).ports v) = (copy G m (p i)).ports v
  member_edges : ∀ i e, occurrence.edges ((copy G n i).edges e) = (copy G m (p i)).edges e
  outputs : ∀ i, (occurrence.ports (.output i)).IsOutput

/-- Selecting any injective ordered list of members gives an actual complete
occurrence; the construction uses only the original tensor recursion. -/
noncomputable def select {n m : Nat} (p : Fin n → Fin m) (injective : Function.Injective p) :
    Selection G p := by
  induction n with
  | zero =>
    let f : MatchEmbedding (copies G 0) (copies G m) := {
      ports := fun v => by cases v with
        | internal v => exact Empty.elim v
        | input i => exact Fin.elim0 i
        | output i => exact Fin.elim0 i
      edges := Empty.elim
      edge_injective := fun e => Empty.elim e
      primitive := fun e => Empty.elim e
      source := fun e => Empty.elim e
      target := fun e => Empty.elim e }
    exact ⟨f.occurrence (fun e => Empty.elim e),fun i => Fin.elim0 i,
      fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    let q : Fin n → Fin m := fun i => p ⟨i.val+1,by omega⟩
    have qi : Function.Injective q := by
      intro i j eq
      have val := congrArg Fin.val (injective eq)
      exact Fin.ext (by change i.val+1=j.val+1 at val; omega)
    let tail := ih q qi
    let first := copy G m (p ⟨0,by omega⟩)
    have apart : ∀ e a, first.edges e ≠ tail.occurrence.edges a := by
      intro e a eq
      obtain ⟨i,b,rfl⟩ := copy_cover G n a
      rw [tail.member_edges] at eq
      apply copy_disjoint G m (p ⟨0,by omega⟩) (q i) ?_ e b eq
      intro same
      have val := congrArg Fin.val (injective same)
      change 0=i.val+1 at val
      omega
    let join := BoxPullWeakening.ReverseComponents.tensorJoin first tail.occurrence apart
    have hi : [Wire.term] ++ List.replicate n Wire.term = List.replicate (n+1) Wire.term := by simp [List.replicate_succ]
    have ho : List.replicate k Wire.term ++ List.replicate (k*n) Wire.term = List.replicate (k*(n+1)) Wire.term := by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm]
    let result : Occurrence (copies G (n+1)) (copies G m) := join.reboundarySource hi ho
    refine ⟨result,?_,?_,?_⟩
    · intro i v
      by_cases zero : i.val = 0
      · have same : i = ⟨0,by omega⟩ := Fin.ext zero
        rw [same]
        change (join.reboundarySource hi ho).ports (Port.cast hi ho ((BoxPullWeakening.ReverseComponents.tensorLeft G (copies G n)).ports v)) = first.ports v
        rw [Occurrence.reboundarySource_ports]
        exact Occurrence.tensorJoin_left first tail.occurrence apart v
      · let j : Fin n := ⟨i.val-1,by omega⟩
        have same : (⟨j.val+1,by omega⟩ : Fin (n+1)) = i := Fin.ext (by dsimp [j]; omega)
        have defcopy : (copy G (n+1) i).ports v =
            Port.cast (by simp [List.replicate_succ])
              (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm])
              ((BoxPullWeakening.ReverseComponents.tensorRight G (copies G n)).ports ((copy G n j).ports v)) := by
          simp only [copy,zero,↓reduceDIte,Occurrence.comp,Occurrence.reboundaryTarget]
          rfl
        rw [defcopy]
        change (join.reboundarySource hi ho).ports (Port.cast hi ho ((BoxPullWeakening.ReverseComponents.tensorRight G (copies G n)).ports ((copy G n j).ports v))) = _
        rw [Occurrence.reboundarySource_ports]
        rw [Occurrence.tensorJoin_right,tail.member_ports]
        change (copy G m (p ⟨j.val+1,by omega⟩)).ports v = _
        rw [same]
    · intro i e
      by_cases zero : i.val = 0
      · have same : i = ⟨0,by omega⟩ := Fin.ext zero
        rw [same]
        rfl
      · let j : Fin n := ⟨i.val-1,by omega⟩
        have same : (⟨j.val+1,by omega⟩ : Fin (n+1)) = i := Fin.ext (by dsimp [j]; omega)
        change join.edges ((copy G (n+1) i).edges e) = _
        simp only [copy,zero,↓reduceDIte,Occurrence.comp,Occurrence.reboundaryTarget]
        change tail.occurrence.edges ((copy G n j).edges e) = _
        rw [tail.member_edges]
        change (copy G m (p ⟨j.val+1,by omega⟩)).edges e = _
        rw [same]
    · intro i
      change (join.ports (.output ⟨i.val,by simpa only [List.length_replicate,List.length_append,Nat.mul_succ,Nat.add_comm] using i.isLt⟩)).IsOutput
      apply Occurrence.tensorJoin_outputs first tail.occurrence apart
      · intro j
        change ((copy G m (p ⟨0,by omega⟩)).ports (.output j)).IsOutput
        rw [copy_output]
        trivial
      · exact tail.outputs

/-- Every source input follows the selected original member index exactly. -/
theorem Selection.input {n m} {p : Fin n → Fin m} (f : Selection G p)
    (i : Fin (List.replicate n Wire.term).length) :
    f.occurrence.ports (.input i) = .input ⟨(p ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ := by
  have eq := f.member_ports ⟨i.val,by simpa using i.isLt⟩ (.input 0)
  simpa only [copy_input] using eq

/-- The private-output block follows the same selected original member,
with its own local ordered outputs unchanged. -/
theorem Selection.output {n m} {p : Fin n → Fin m} (f : Selection G p)
    (i : Fin n) (j : Fin (List.replicate k Wire.term).length) :
    f.occurrence.ports (.output ⟨k*i.val+j.val,by
      have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      have h := j.isLt; simp only [Nat.mul_succ,List.length_replicate] at *; omega⟩) =
      .output ⟨k*(p i).val+j.val,by
        have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt (p i).isLt)
        have h := j.isLt; simp only [Nat.mul_succ,List.length_replicate] at *; omega⟩ := by
  simpa only [copy_output] using f.member_ports i (.output j)

/-- A bijective member selection covers every original edge. -/
theorem Selection.cover {n m} {p : Fin n → Fin m} (f : Selection G p)
    (surjective : Function.Surjective p) : Function.Surjective f.occurrence.edges := by
  intro e
  obtain ⟨i,a,rfl⟩ := copy_cover G m e
  obtain ⟨j,rfl⟩ := surjective i
  exact ⟨(copy G n j).edges a,f.member_edges j a⟩

/-- Any bijection of original members is a complete recursive boundary
isomorphism of the actual ordered-copy graph. -/
noncomputable def reindex {n m} (p : Bijection (Fin n) (Fin m)) :
    BoundaryIso (copies G n) (copies G m) :=
  (select G p.toFun (fun _ _ eq => p.injective eq)).occurrence.boundaryIso_of_edge_surjective
    (fun i => by rw [Selection.input]; trivial)
    (select G p.toFun (fun _ _ eq => p.injective eq)).outputs
    ((select G p.toFun (fun _ _ eq => p.injective eq)).cover G (fun i => ⟨p.invFun i,p.right_inv i⟩))

end Hypernets.Copying.Parametricity.FamilyComponents
