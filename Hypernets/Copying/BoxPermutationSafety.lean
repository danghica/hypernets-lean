import Hypernets.Copying.BoxPermutationRule

/-! Structural safety of the concrete BPerm pair. These are not proofs of
input-safety or robustness for an execution semantics. -/
namespace Hypernets.Copying.BoxPermutation
open Graph
variable {d n k h : Nat} (G : Hypernet d [.term] (environmentInterface (n+k) h))

/-- The fresh outer box has no hole; binding paths are checked in its unchanged body. -/
theorem bindingFree_box_iff : BindingFree (box (bound := n) (freeVariables := k) G) ↔ BindingFree G := by
  constructor
  · intro h
    exact ⟨h.1 (0 : Fin 1), h.2.2 (0 : Fin 1)⟩
  · intro h
    refine ⟨fun _ => h.1,?_,fun _ => h.2⟩
    intro e f _ _ hole
    obtain ⟨x,eq⟩ := hole
    contradiction

/-- The compensated rule preserves precisely the same binding-free condition. -/
theorem bindingFree_right (p : Pair n k h) : BindingFree (right G p) ↔ BindingFree G :=
  (InterfacePermutation.bindingFree_iff _ _).trans
    ((bindingFree_box_iff _).trans (InterfacePermutation.bindingFree_iff _ _))

theorem Step.allLabels {d I O} {G H : Hypernet d I O} (s : Step G H) (P : Primitive → Prop) :
    AllLabels P G ↔ AllLabels P H := by
  cases s with
  | @permute d n k h G p =>
    constructor
    · intro h e; exact h (0 : Fin 1)
    · intro h e; exact h (0 : Fin 1)

theorem Step.bindingFree {d I O} {G H : Hypernet d I O} (s : Step G H) : BindingFree G ↔ BindingFree H := by
  cases s with
  | permute G p =>
    exact (bindingFree_box_iff _).trans ((InterfacePermutation.bindingFree_iff G p.body.symm).trans
      ((bindingFree_box_iff G).symm.trans (InterfacePermutation.bindingFree_iff _ p.outer.symm).symm))

/-- Fixed-boundary isomorphism closure does not weaken the safety statement. -/
theorem UpToIso.bindingFree {d I O} {G H : Hypernet d I O} (s : UpToIso G H) : BindingFree G ↔ BindingFree H := by
  cases s with
  | witness f s g =>
    exact (BoundaryIso.ofDeepIso f).bindingFree_iff.trans
        (s.bindingFree.trans (BoundaryIso.ofDeepIso g).bindingFree_iff)

theorem UpToIso.allLabels {d I O} {G H : Hypernet d I O} (s : UpToIso G H) (P : Primitive → Prop) :
    AllLabels P G ↔ AllLabels P H := by
  cases s with
  | witness f s g =>
    exact ((BoundaryIso.ofDeepIso f).allLabels_iff P).trans
        ((s.allLabels P).trans ((BoundaryIso.ofDeepIso g).allLabels_iff P))
end Hypernets.Copying.BoxPermutation
