import Hypernets.Copying.BoundaryInstance

/-! The atomic cases of bijective renaming for the unchanged Figure 16 translation. -/
namespace Hypernets.Copying.Translation
open Graph

/-- Precisely the three leaf constructors, with the original scoped terms. -/
inductive Atomic {k h} : Term k h → Prop where
  | var (i : Fin k) : Atomic (.var i)
  | atom (a : Fin h) : Atomic (.atom a)
  | constant (c : Constant) : Atomic (.const c)

/-- Every atomic translation respects bijective resource renaming. The depth
transport is the existing syntactic depth-renaming identity, not a new translation. -/
theorem atomic_rename {k h} (t : Term k h) (leaf : Atomic t)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (term t)
      (castDepth (depth_rename t ρ.toFun α.toFun) (term (Term.rename ρ.toFun α.toFun t)))) := by
  cases leaf with
  | var i => exact ⟨variableTerm_rename 0 ρ α i⟩
  | atom a => exact ⟨atom_rename 0 ρ α a⟩
  | constant c => exact ⟨constant_rename 0 ρ α c⟩
end Hypernets.Copying.Translation
