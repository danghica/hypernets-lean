import Hypernets.Copying.TensorBoundaryActions

/-! Every typed environment permutation extends through the literal single-use distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SingleUseBoundary
open Graph EnvironmentPermutation

def iso (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    BoundaryIso (Translation.singleUse d k h) (Translation.singleUse d k h) :=
  BoundaryIso.castInterfaces _ rfl _ rfl
    ((Distributor.boundaryIso .term 1 d ρ).tensor (Distributor.boundaryIso .atom 1 d α))

theorem input_term (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (i : Fin k) :
    (iso d ρ α).ports.toFun (.input (termIndex i)) = .input (termIndex (ρ.toFun i)) := by
  let f := Distributor.boundaryIso .term 1 d ρ
  let g := Distributor.boundaryIso .atom 1 d α
  have law := f.tensor_input_left g (Distributor.inputIndex .term ⟨i,⟨0,by simp⟩⟩)
  have act := Distributor.resourcePorts_input (m := 1) .term ρ i ⟨0,by simp⟩
  change f.ports.toFun (.input _) = .input _ at act
  rw [f.map_input] at act
  dsimp only [BoundaryIso.inputs] at law
  rw [Port.input.inj act] at law
  exact BoundaryIso.castInterfaces_input _ rfl _ rfl (f.tensor g) _ _ law

theorem input_atom (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (a : Fin h) :
    (iso d ρ α).ports.toFun (.input (atomIndex a)) = .input (atomIndex (α.toFun a)) := by
  let f := Distributor.boundaryIso .term 1 d ρ
  let g := Distributor.boundaryIso .atom 1 d α
  have law := f.tensor_input_right g (Distributor.inputIndex .atom ⟨a,⟨0,by simp⟩⟩)
  have act := Distributor.resourcePorts_input (m := 1) .atom α a ⟨0,by simp⟩
  change g.ports.toFun (.input _) = .input _ at act
  rw [g.map_input] at act
  dsimp only [BoundaryIso.inputs] at law
  rw [Port.input.inj act] at law
  have hh := BoundaryIso.castInterfaces_input
    (show environmentInterface (k*1) (h*1) = environmentInterface k h by simp) rfl
    (show environmentInterface (k*1) (h*1) = environmentInterface k h by simp) rfl (f.tensor g) _ _ law
  simpa only [iso,f,g,Net.Tensor.join,List.length_replicate,Nat.mul_one,Fin.cast,Distributor.inputIndex,FinGrid.index,Nat.mul_zero,Nat.add_zero,atomIndex] using hh

theorem output_term (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (i : Fin k) :
    (iso d ρ α).ports.toFun (.output (termIndex i)) = .output (termIndex (ρ.toFun i)) := by
  have law := (Distributor.boundaryIso .term 1 d ρ).tensor_output_left (Distributor.boundaryIso .atom 1 d α)
    ⟨i.val,by simpa using i.isLt⟩
  rw [Distributor.outputIndex_eq] at law
  have hh := BoundaryIso.castInterfaces_output
    (show environmentInterface (k*1) (h*1) = environmentInterface k h by simp) rfl
    (show environmentInterface (k*1) (h*1) = environmentInterface k h by simp) rfl _ _ _ law
  simpa only [iso,Net.Tensor.join,List.length_replicate,Fin.cast,atomIndex,termIndex] using hh

theorem output_atom (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (a : Fin h) :
    (iso d ρ α).ports.toFun (.output (atomIndex a)) = .output (atomIndex (α.toFun a)) := by
  have law := (Distributor.boundaryIso .term 1 d ρ).tensor_output_right (Distributor.boundaryIso .atom 1 d α)
    ⟨a.val,by simpa using a.isLt⟩
  rw [Distributor.outputIndex_eq] at law
  have hh := BoundaryIso.castInterfaces_output
    (show environmentInterface (k*1) (h*1) = environmentInterface k h by simp) rfl
    (show environmentInterface (k*1) (h*1) = environmentInterface k h by simp) rfl _ _ _ law
  simpa only [iso,Net.Tensor.join,List.length_replicate,Fin.cast,atomIndex,termIndex] using hh
end Hypernets.Copying.SingleUseBoundary

namespace Hypernets.Copying.SingleUseBoundary
open Graph EnvironmentPermutation
variable {k h : Nat}
    (π : Bijection (Fin (environmentInterface k h).length) (Fin (environmentInterface k h).length))
    (typed : ∀ i, (environmentInterface k h).get (π.toFun i) = (environmentInterface k h).get i)

/-- Extend any typed environment permutation, with no additional matching premise. -/
def ofTyped (d : Nat) : BoundaryIso (Translation.singleUse d k h) (Translation.singleUse d k h) :=
  iso d (terms π typed) (atoms π typed)

include typed in
theorem ofTyped_input (d : Nat) (j : Fin (environmentInterface k h).length) :
    (ofTyped π typed d).ports.toFun (.input j) = .input (π.toFun j) := by
  by_cases hj : j.val < k
  · let i : Fin k := ⟨j.val,hj⟩
    have eq : j = termIndex (h := h) i := rfl
    rw [eq,term_action π typed]
    exact input_term d (terms π typed) (atoms π typed) i
  · let a : Fin h := ⟨j.val-k,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at this; omega⟩
    have eq : j = atomIndex (k := k) a := Fin.ext (by dsimp [a,atomIndex]; omega)
    rw [eq,atom_action π typed]
    exact input_atom d (terms π typed) (atoms π typed) a

include typed in
theorem ofTyped_output (d : Nat) (j : Fin (environmentInterface k h).length) :
    (ofTyped π typed d).ports.toFun (.output j) = .output (π.toFun j) := by
  by_cases hj : j.val < k
  · let i : Fin k := ⟨j.val,hj⟩
    have eq : j = termIndex (h := h) i := rfl
    rw [eq,term_action π typed]
    exact output_term d (terms π typed) (atoms π typed) i
  · let a : Fin h := ⟨j.val-k,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at this; omega⟩
    have eq : j = atomIndex (k := k) a := Fin.ext (by dsimp [a,atomIndex]; omega)
    rw [eq,atom_action π typed]
    exact output_atom d (terms π typed) (atoms π typed) a
end Hypernets.Copying.SingleUseBoundary
