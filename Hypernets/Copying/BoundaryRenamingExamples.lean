import Hypernets.Copying.DistributorSerialRenaming

/-! Regression witnesses for exact compatibility, including empty forests and
nontrivial resource swaps. No transition semantics is postulated here. -/
namespace Hypernets.Copying.BoundaryRenamingExamples
open Graph

def swapTwo : Bijection (Fin 2) (Fin 2) where
  toFun i := ⟨1-i.val,by omega⟩
  invFun i := ⟨1-i.val,by omega⟩
  left_inv i := by apply Fin.ext; simp; omega
  right_inv i := by apply Fin.ext; simp; omega

/-- Two-use atom sharing with a nontrivial permutation and all distributors retained. -/
def twoAtomUses (d : Nat) := Distributor.serial_singleIso .atom 2 d swapTwo

/-- A swap on only one side of the glued interface cannot pass the compatibility check. -/
theorem unmatched_swap (s : ShareSort) (m d : Nat) :
    ¬ BoundarySerial.Compatible (Distributor.boundaryIso s m d swapTwo)
      (Distributor.singleIso s d (Bijection.refl (Fin 2))) := by
  intro h
  have eq := (Distributor.single_compatible_iff s m d swapTwo (Bijection.refl _)).mp h
  have atZero := congrFun eq 0
  have vals := congrArg Fin.val atZero
  contradiction

/-- An empty forest requires no nonemptiness hypothesis. -/
def emptyForest (s : ShareSort) (m d : Nat) :=
  Distributor.serial_singleIso s m d (Bijection.refl (Fin 0))

/-- Zero-use weakening forests are included, rather than discarded as a special case. -/
def weakeningForest (s : ShareSort) {k} (d : Nat) (π : Bijection (Fin k) (Fin k)) :=
  Distributor.serial_singleIso s 0 d π

/-- Any original binding-free configuration remains safe under a compatible
pair of boundary renamings; the result checks all nested bodies as well. -/
theorem serial_bindingFree_iff {d I J K I' J' K'}
    {G : Hypernet d I J} {H : Hypernet d J K}
    {G' : Hypernet d I' J'} {H' : Hypernet d J' K'}
    (f : BoundaryIso G G') (g : BoundaryIso H H') (h : BoundarySerial.Compatible f g) :
    BindingFree (Serial.net G H) ↔ BindingFree (Serial.net G' H') :=
  (BoundarySerial.iso f g h).bindingFree_iff
end Hypernets.Copying.BoundaryRenamingExamples
