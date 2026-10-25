import Hypernets.Copying.PairBoundaryCoordinates

/-! Exact boundary actions of the original multi-use environment distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MultiUseBoundary
open Graph EnvironmentPermutation

def iso (d m : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    BoundaryIso (Translation.environmentDistributor d k h m) (Translation.environmentDistributor d k h m) :=
  (Distributor.boundaryIso .term m d ρ).tensor (Distributor.boundaryIso .atom m d α)

theorem output_term (d m : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (i : Fin k) :
    (iso d m ρ α).ports.toFun (.output (termIndex i)) = .output (termIndex (ρ.toFun i)) := by
  have law := (Distributor.boundaryIso .term m d ρ).tensor_output_left (Distributor.boundaryIso .atom m d α)
    ⟨i.val,by simpa using i.isLt⟩
  rw [Distributor.outputIndex_eq] at law
  exact law

theorem output_atom (d m : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (a : Fin h) :
    (iso d m ρ α).ports.toFun (.output (atomIndex a)) = .output (atomIndex (α.toFun a)) := by
  have law := (Distributor.boundaryIso .term m d ρ).tensor_output_right (Distributor.boundaryIso .atom m d α)
    ⟨a.val,by simpa using a.isLt⟩
  rw [Distributor.outputIndex_eq] at law
  simpa only [iso,Net.Tensor.join,List.length_replicate,atomIndex] using law

theorem input_term (d m : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (i : Fin k) (u : Fin m) :
    (iso d m ρ α).ports.toFun (.input (termIndex ⟨i.val+k*u.val,(FinGrid.index i u).isLt⟩)) =
      .input (termIndex ⟨(ρ.toFun i).val+k*u.val,(FinGrid.index (ρ.toFun i) u).isLt⟩) := by
  let f := Distributor.boundaryIso .term m d ρ
  let g := Distributor.boundaryIso .atom m d α
  have law := f.tensor_input_left g (Distributor.inputIndex .term ⟨i,⟨u.val,by simpa using u.isLt⟩⟩)
  have act := Distributor.resourcePorts_input (m := m) .term ρ i ⟨u.val,by simpa using u.isLt⟩
  change f.ports.toFun (.input _) = .input _ at act
  rw [f.map_input] at act
  dsimp only [BoundaryIso.inputs] at law
  rw [Port.input.inj act] at law
  exact law

theorem input_atom (d m : Nat) {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (a : Fin h) (u : Fin m) :
    (iso d m ρ α).ports.toFun (.input (atomIndex ⟨a.val+h*u.val,(FinGrid.index a u).isLt⟩)) =
      .input (atomIndex ⟨(α.toFun a).val+h*u.val,(FinGrid.index (α.toFun a) u).isLt⟩) := by
  let f := Distributor.boundaryIso .term m d ρ
  let g := Distributor.boundaryIso .atom m d α
  have law := f.tensor_input_right g (Distributor.inputIndex .atom ⟨a,⟨u.val,by simpa using u.isLt⟩⟩)
  have act := Distributor.resourcePorts_input (m := m) .atom α a ⟨u.val,by simpa using u.isLt⟩
  change g.ports.toFun (.input _) = .input _ at act
  rw [g.map_input] at act
  dsimp only [BoundaryIso.inputs] at law
  rw [Port.input.inj act] at law
  simpa only [iso,f,g,Net.Tensor.join,List.length_replicate,Distributor.inputIndex,FinGrid.index,atomIndex] using law

variable {k h : Nat}
    (π : Bijection (Fin (environmentInterface k h).length) (Fin (environmentInterface k h).length))
    (typed : ∀ i, (environmentInterface k h).get (π.toFun i) = (environmentInterface k h).get i)

def ofTyped (d m : Nat) := iso d m (terms π typed) (atoms π typed)

include typed in
theorem ofTyped_output (d m : Nat) (j : Fin (environmentInterface k h).length) :
    (ofTyped π typed d m).ports.toFun (.output j) = .output (π.toFun j) := by
  by_cases hj : j.val < k
  · let i : Fin k := ⟨j.val,hj⟩
    have eq : j = termIndex (h := h) i := rfl
    rw [eq,term_action π typed]
    exact output_term d m (terms π typed) (atoms π typed) i
  · let a : Fin h := ⟨j.val-k,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at this; omega⟩
    have eq : j = atomIndex (k := k) a := Fin.ext (by dsimp [a,atomIndex]; omega)
    rw [eq,atom_action π typed]
    exact output_atom d m (terms π typed) (atoms π typed) a

include typed in
/-- The two-use distributor action matches the original pair shuffle, component by component. -/
theorem ofTyped_pair_input (d : Nat) (b : Bool) (j : Fin (environmentInterface k h).length) :
    (ofTyped π typed d 2).ports.toFun (.input (PairBoundary.index b j)) =
      .input (PairBoundary.index b (π.toFun j)) := by
  by_cases hj : j.val < k
  · let i : Fin k := ⟨j.val,hj⟩
    have eq : j = termIndex (h := h) i := rfl
    rw [eq,term_action π typed,PairBoundary.term_index,PairBoundary.term_index]
    exact input_term d 2 (terms π typed) (atoms π typed) i ⟨PairBoundary.use b,by cases b <;> decide⟩
  · let a : Fin h := ⟨j.val-k,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at this; omega⟩
    have eq : j = atomIndex (k := k) a := Fin.ext (by dsimp [a,atomIndex]; omega)
    rw [eq,atom_action π typed,PairBoundary.atom_index,PairBoundary.atom_index]
    exact input_atom d 2 (terms π typed) (atoms π typed) a ⟨PairBoundary.use b,by cases b <;> decide⟩
end Hypernets.Copying.MultiUseBoundary
