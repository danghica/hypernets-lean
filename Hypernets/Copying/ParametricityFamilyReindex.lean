import Hypernets.Copying.ParametricityCopyReindex
import Hypernets.Copying.BoundarySourceReboundary
import Hypernets.Copying.ParametricityFamilyLiteral

/-! Independent ordered permutations of the two original abstraction blocks.
The same numerical input action applies to both paper sides, and each private
left output follows its own abstraction's input. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.FamilyComponents
open Graph Opening
variable {d k : Nat} (G : Hypernet d [.term] (List.replicate k .term))

/-- Reindexing sends each actual input to its designated original member. -/
theorem reindex_input {n m} (p : Bijection (Fin n) (Fin m))
    (i : Fin (List.replicate n Wire.term).length) :
    (reindex G p).ports.toFun (.input i) = .input ⟨(p.toFun ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ :=
  (select G p.toFun (fun _ _ eq => p.injective eq)).input G i

/-- Reindexing keeps the complete ordered output row of each original copy. -/
theorem reindex_output {n m} (p : Bijection (Fin n) (Fin m))
    (i : Fin n) (j : Fin (List.replicate k Wire.term).length) :
    (reindex G p).ports.toFun (.output ⟨k*i.val+j.val,by
      have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      have h := j.isLt; simp only [Nat.mul_succ,List.length_replicate] at *; omega⟩) =
      .output ⟨k*(p.toFun i).val+j.val,by
        have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt (p.toFun i).isLt)
        have h := j.isLt; simp only [Nat.mul_succ,List.length_replicate] at *; omega⟩ :=
  (select G p.toFun (fun _ _ eq => p.injective eq)).output G i j

variable (A B : Hypernet d [.term] (List.replicate k .term)) {m n : Nat}
    (p : Bijection (Fin m) (Fin m)) (q : Bijection (Fin n) (Fin n))

/-- A full recursive reindexing of both literal family blocks. -/
noncomputable def reindexFamily : BoundaryIso (family A B m n) (family A B m n) :=
  ((reindex A p).tensor (reindex B q)).reboundaryBoth _ _ _ _

/-- The full actual family port map includes the explicit interface casts. -/
theorem reindexFamily_port (v : (family A B m n).Vertex) :
    (reindexFamily A B p q).ports.toFun v =
      Port.cast (by rw [List.replicate_append_replicate])
        (by rw [List.replicate_append_replicate,Nat.mul_add])
        (((reindex A p).tensor (reindex B q)).ports.toFun
          (Port.cast (by rw [List.replicate_append_replicate])
            (by rw [List.replicate_append_replicate,Nat.mul_add]) v)) := by
  change (BoundaryIso.interfaceEquality _ _ _).ports.toFun
    (((reindex A p).tensor (reindex B q)).ports.toFun
      ((BoundaryIso.interfaceEquality _ _ _).ports.invFun v)) = _
  rw [BoundaryIso.interfaceEquality_inverse,BoundaryIso.interfaceEquality_port]

/-- Every large input follows precisely the selected permutation of its block. -/
theorem reindexFamily_large_input (i : Fin m) :
    (reindexFamily A B p q).ports.toFun (.input ⟨i.val,by simp; omega⟩) =
      .input ⟨(p.toFun i).val,by simp; have := (p.toFun i).isLt; omega⟩ := by
  rw [reindexFamily_port]
  have input := BoundaryIso.tensor_input_left (reindex A p) (reindex B q)
    ⟨i.val,by simpa using i.isLt⟩
  have selected := (reindex A p).map_input ⟨i.val,by simpa using i.isLt⟩
  rw [reindex_input] at selected
  have eq := Port.input.inj selected
  change _ = Port.input (Net.Tensor.join (List.replicate m Wire.term) (List.replicate n Wire.term)
    ⟨false,(reindex A p).inputMap ⟨i.val,by simpa using i.isLt⟩⟩) at input
  rw [← eq] at input
  simpa only [Net.Tensor.join,List.length_replicate,Port.cast,Fin.cast] using congrArg (Port.cast
    (show List.replicate m Wire.term ++ List.replicate n Wire.term = List.replicate (m+n) Wire.term from by rw [List.replicate_append_replicate])
    (show List.replicate (k*m) Wire.term ++ List.replicate (k*n) Wire.term = List.replicate (k*(m+n)) Wire.term from by rw [List.replicate_append_replicate,Nat.mul_add])) input

/-- Every small input follows its own block permutation after the large block. -/
theorem reindexFamily_small_input (i : Fin n) :
    (reindexFamily A B p q).ports.toFun (.input ⟨m+i.val,by simp⟩) =
      .input ⟨m+(q.toFun i).val,by simp⟩ := by
  rw [reindexFamily_port]
  have input := BoundaryIso.tensor_input_right (reindex A p) (reindex B q)
    ⟨i.val,by simpa using i.isLt⟩
  have selected := (reindex B q).map_input ⟨i.val,by simpa using i.isLt⟩
  rw [reindex_input] at selected
  have eq := Port.input.inj selected
  change _ = Port.input (Net.Tensor.join (List.replicate m Wire.term) (List.replicate n Wire.term)
    ⟨true,(reindex B q).inputMap ⟨i.val,by simpa using i.isLt⟩⟩) at input
  rw [← eq] at input
  simpa only [Net.Tensor.join,List.length_replicate,Port.cast,Fin.cast] using congrArg (Port.cast
    (show List.replicate m Wire.term ++ List.replicate n Wire.term = List.replicate (m+n) Wire.term from by rw [List.replicate_append_replicate])
    (show List.replicate (k*m) Wire.term ++ List.replicate (k*n) Wire.term = List.replicate (k*(m+n)) Wire.term from by rw [List.replicate_append_replicate,Nat.mul_add])) input

/-- Every private output of a large member follows that complete member. -/
theorem reindexFamily_large_output (i : Fin m) (j : Fin (List.replicate k Wire.term).length) :
    (reindexFamily A B p q).ports.toFun (.output ⟨k*i.val+j.val,by
      have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      have h := j.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩) =
      .output ⟨k*(p.toFun i).val+j.val,by
        have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt (p.toFun i).isLt)
        have h := j.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩ := by
  rw [reindexFamily_port]
  let x : Fin (List.replicate (k*m) Wire.term).length := ⟨k*i.val+j.val,by
    have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
    have h := j.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩
  have output := BoundaryIso.tensor_output_left (reindex A p) (reindex B q) x
  have selected := (reindex A p).map_output x
  rw [show x = ⟨k*i.val+j.val,x.isLt⟩ from rfl,reindex_output] at selected
  have eq := Port.output.inj selected
  change _ = Port.output (Net.Tensor.join (List.replicate (k*m) Wire.term) (List.replicate (k*n) Wire.term)
    ⟨false,(reindex A p).outputMap x⟩) at output
  rw [← eq] at output
  simpa only [Net.Tensor.join,List.length_replicate,Port.cast,Fin.cast] using congrArg (Port.cast
    (show List.replicate m Wire.term ++ List.replicate n Wire.term = List.replicate (m+n) Wire.term from by rw [List.replicate_append_replicate])
    (show List.replicate (k*m) Wire.term ++ List.replicate (k*n) Wire.term = List.replicate (k*(m+n)) Wire.term from by rw [List.replicate_append_replicate,Nat.mul_add])) output

/-- Every private output of a small member keeps its local order and offset. -/
theorem reindexFamily_small_output (i : Fin n) (j : Fin (List.replicate k Wire.term).length) :
    (reindexFamily A B p q).ports.toFun (.output ⟨k*m+(k*i.val+j.val),by
      have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      have h := j.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩) =
      .output ⟨k*m+(k*(q.toFun i).val+j.val),by
        have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt (q.toFun i).isLt)
        have h := j.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩ := by
  rw [reindexFamily_port]
  let x : Fin (List.replicate (k*n) Wire.term).length := ⟨k*i.val+j.val,by
    have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
    have h := j.isLt; simp only [List.length_replicate,Nat.mul_add,Nat.mul_succ] at *; omega⟩
  have output := BoundaryIso.tensor_output_right (reindex A p) (reindex B q) x
  have selected := (reindex B q).map_output x
  rw [show x = ⟨k*i.val+j.val,x.isLt⟩ from rfl,reindex_output] at selected
  have eq := Port.output.inj selected
  change _ = Port.output (Net.Tensor.join (List.replicate (k*m) Wire.term) (List.replicate (k*n) Wire.term)
    ⟨true,(reindex B q).outputMap x⟩) at output
  rw [← eq] at output
  simpa only [Net.Tensor.join,List.length_replicate,Port.cast,Fin.cast] using congrArg (Port.cast
    (show List.replicate m Wire.term ++ List.replicate n Wire.term = List.replicate (m+n) Wire.term from by rw [List.replicate_append_replicate])
    (show List.replicate (k*m) Wire.term ++ List.replicate (k*n) Wire.term = List.replicate (k*(m+n)) Wire.term from by rw [List.replicate_append_replicate,Nat.mul_add])) output

/-- The independent block permutations as one ordered external index map. -/
def blockIndex (i : Fin (m+n)) : Fin (m+n) :=
  if bound : i.val < m then ⟨(p.toFun ⟨i.val,bound⟩).val,by have := (p.toFun ⟨i.val,bound⟩).isLt; omega⟩
  else ⟨m+(q.toFun ⟨i.val-m,by have := i.isLt; omega⟩).val,by have := (q.toFun ⟨i.val-m,by have := i.isLt; omega⟩).isLt; omega⟩

/-- The complete family input action is independent of its output arity. -/
theorem reindexFamily_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (reindexFamily A B p q).ports.toFun (.input i) =
      .input ⟨(blockIndex p q ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ := by
  by_cases bound : i.val < m
  · simpa only [blockIndex,bound,↓reduceDIte] using
      reindexFamily_large_input A B p q ⟨i.val,bound⟩
  · let j : Fin n := ⟨i.val-m,by have := i.isLt; simp only [List.length_replicate] at this; omega⟩
    have same : (⟨m+j.val,by simp⟩ : Fin (List.replicate (m+n) Wire.term).length) = i :=
      Fin.ext (by dsimp [j]; omega)
    simpa only [same,blockIndex,bound,↓reduceDIte] using reindexFamily_small_input A B p q j

/-- For the private one-output family the output and input actions coincide. -/
theorem reindexFamily_output_one (A B : Hypernet d [.term] (List.replicate 1 .term))
    (i : Fin (List.replicate (1*(m+n)) Wire.term).length) :
    (reindexFamily A B p q).ports.toFun (.output i) =
      .output ⟨(blockIndex p q ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩ := by
  by_cases bound : i.val < m
  · simpa only [blockIndex,bound,↓reduceDIte,Nat.one_mul,Nat.add_zero] using
      reindexFamily_large_output A B p q ⟨i.val,bound⟩ ⟨0,by simp⟩
  · let j : Fin n := ⟨i.val-m,by have := i.isLt; simp only [List.length_replicate,Nat.one_mul] at this; omega⟩
    have same : (⟨m+j.val,by simpa using (Nat.add_lt_add_left j.isLt m)⟩ :
        Fin (List.replicate (1*(m+n)) Wire.term).length) = i := Fin.ext (by dsimp [j]; omega)
    have eq := reindexFamily_small_output A B p q j ⟨0,by simp⟩
    simp only [Nat.one_mul,Nat.add_zero] at eq
    simpa only [same,blockIndex,bound,↓reduceDIte] using eq

end Hypernets.Copying.Parametricity.FamilyComponents
