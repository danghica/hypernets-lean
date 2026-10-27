import Hypernets.Copying.AllocationRefocusing

/-! Rootedness respects the concrete search representation and padding laws. -/
namespace Hypernets.Copying.Search
open Graph

/-- A transport between single-input graphs necessarily preserves that input. -/
theorem Transport.sole_input {d r O K} {G : Hypernet d [.term] O} {H : Hypernet r [.term] K}
    (f : Transport G H) : f.ports.toFun (.input 0) = .input 0 := by
  have input := (f.input_iff (.input 0)).mpr trivial
  cases eq : f.ports.toFun (.input 0) with
  | internal x => rw [eq] at input; cases input
  | output j => rw [eq] at input; cases input
  | input j => have zero : j = 0 := Fin.ext (by have := j.isLt; change j.val < 1 at this; change j.val = 0; omega)
               rw [zero]

theorem Transport.rooted_iff {d r O K} {G : Hypernet d [.term] O} {H : Hypernet r [.term] K}
    (f : Transport G H) (p : Position G) :
    RootedFrom H 0 (f.positions.toFun p) ↔ RootedFrom G 0 p := by
  have root : f.positions.toFun (.search,.input 0) = (.search,.input 0) := Prod.ext rfl f.sole_input
  unfold RootedFrom
  exact exists_congr (fun n => by rw [← root]; exact f.machine_steps_iff n _ p)

theorem rooted_padTo_iff {d O} (G : Hypernet d [.term] O) (N : Nat) (bound : d ≤ N) (p : Position G) :
    RootedFrom (Translation.padTo N bound G) 0 ((padTo G N bound).positions.toFun p) ↔ RootedFrom G 0 p :=
  (padTo G N bound).rooted_iff p
end Hypernets.Copying.Search
