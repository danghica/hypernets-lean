import Hypernets.Copying.BoundaryRenamingExamples

/-! A typed permutation of a term/atom environment splits into its two resource sorts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.EnvironmentPermutation
open Graph

def termIndex {k h} (i : Fin k) : Fin (environmentInterface k h).length := ⟨i.val,by simp [environmentInterface]; omega⟩
def atomIndex {k h} (a : Fin h) : Fin (environmentInterface k h).length := ⟨k+a.val,by simp [environmentInterface]⟩

theorem term_label {k h} (i : Fin k) : (environmentInterface k h).get (termIndex i) = .term := by
  simp [environmentInterface,termIndex,List.getElem_append,i.isLt]

theorem atom_label {k h} (a : Fin h) : (environmentInterface k h).get (atomIndex a) = .atom := by
  simp [environmentInterface,atomIndex,List.getElem_append]

/-- A position is a variable exactly when its wire has term type. -/
theorem term_iff {k h} (j : Fin (environmentInterface k h).length) :
    (environmentInterface k h).get (j) = .term ↔ j.val < k := by
  change (List.replicate k Wire.term ++ List.replicate h Wire.atom)[j.val]'j.isLt = _ ↔ _
  rw [List.getElem_append]
  by_cases hj : j.val < k <;> simp [hj] <;> omega

/-- The atom block begins immediately after the term block. -/
theorem atom_iff {k h} (j : Fin (environmentInterface k h).length) :
    (environmentInterface k h).get (j) = .atom ↔ k ≤ j.val := by
  change (List.replicate k Wire.term ++ List.replicate h Wire.atom)[j.val]'j.isLt = _ ↔ _
  rw [List.getElem_append]
  by_cases hj : j.val < k <;> simp [hj] <;> omega

variable {k h : Nat}
    (π : Bijection (Fin (environmentInterface k h).length) (Fin (environmentInterface k h).length))
    (typed : ∀ i, (environmentInterface k h).get (π.toFun i) = (environmentInterface k h).get (i))

def termMap (i : Fin k) : Fin k :=
  ⟨(π.toFun (termIndex i)).val,(term_iff _).mp ((typed _).trans (term_label i))⟩

def atomMap (a : Fin h) : Fin h :=
  let j := π.toFun (atomIndex a)
  ⟨j.val-k,by have ha := a.isLt; have hj := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at hj; omega⟩

theorem term_action (i : Fin k) : π.toFun (termIndex i) = termIndex (termMap π typed i) := rfl

include typed in
theorem atom_action (a : Fin h) : π.toFun (atomIndex a) = atomIndex (atomMap π a) := by
  apply Fin.ext
  have hb := (atom_iff _).mp ((typed _).trans (atom_label a))
  change (π.toFun (atomIndex a)).val = k + ((π.toFun (atomIndex a)).val-k)
  omega

include typed in
theorem inverse_typed (i) : (environmentInterface k h).get (π.invFun i) = (environmentInterface k h).get (i) := by
  have ht := typed (π.invFun i)
  rw [π.right_inv] at ht
  exact ht.symm

def terms : Bijection (Fin k) (Fin k) where
  toFun := termMap π typed
  invFun := termMap π.symm (inverse_typed π typed)
  left_inv i := by
    apply Fin.ext
    have eq := π.left_inv (termIndex i)
    rw [term_action π typed] at eq
    exact congrArg (fun j : Fin (environmentInterface k h).length => j.val) eq
  right_inv i := by
    apply Fin.ext
    have eq := π.right_inv (termIndex i)
    change π.toFun (π.symm.toFun (termIndex i)) = _ at eq
    rw [term_action π.symm (inverse_typed π typed)] at eq
    exact congrArg (fun j : Fin (environmentInterface k h).length => j.val) eq

def atoms (typed : ∀ i, (environmentInterface k h).get (π.toFun i) = (environmentInterface k h).get (i)) : Bijection (Fin h) (Fin h) where
  toFun := atomMap π
  invFun := atomMap π.symm
  left_inv a := by
    have eq := π.left_inv (atomIndex a)
    rw [atom_action π typed] at eq
    change π.symm.toFun (atomIndex (atomMap π a)) = _ at eq
    rw [atom_action π.symm (inverse_typed π typed)] at eq
    have vals := congrArg (fun j : Fin (environmentInterface k h).length => j.val) eq
    apply Fin.ext
    simp only [atomIndex] at vals
    omega
  right_inv a := by
    have eq := π.right_inv (atomIndex a)
    change π.toFun (π.symm.toFun (atomIndex a)) = _ at eq
    rw [atom_action π.symm (inverse_typed π typed),atom_action π typed] at eq
    have vals := congrArg (fun j : Fin (environmentInterface k h).length => j.val) eq
    apply Fin.ext
    simp only [atomIndex] at vals
    omega
end Hypernets.Copying.EnvironmentPermutation
