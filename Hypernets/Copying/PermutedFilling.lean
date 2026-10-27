import Hypernets.Copying.BPermForwardTransport

/-! External output permutation of an existing recursive filling certificate,
implemented by an actual permuted corolla context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate} {d I O} {G H : Hypernet d I O}

noncomputable def permuted (w : FillingWitness T G H) (p : TypedPermutation O) :
    FillingWitness T (InterfacePermutation.net G p) (InterfacePermutation.net H p) := by
  cases d with
  | zero =>
    let a := primitiveLabel 0 (.hole ⟨0,I,O⟩)
    let C := InterfacePermutation.PlugContext.context a p
    let F := SingleExpansion.family C (0 : Fin 1) G
    let K := SingleExpansion.family C (0 : Fin 1) H
    have components : ∀ e, FillingWitness T (F e) (K e) := by
      intro e
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      simpa only [F,K,SingleExpansion.selected] using w
    exact (expand C components).congr
      ((SingleExpansion.iso C (0 : Fin 1) G).trans (InterfacePermutation.PlugContext.iso a p G))
      ((SingleExpansion.iso C (0 : Fin 1) H).trans (InterfacePermutation.PlugContext.iso a p H))
  | succ d =>
    let a := primitiveLabel (d+1) (.hole ⟨0,I,O⟩)
    let C := InterfacePermutation.PlugContext.context a p
    let F := SingleExpansion.family C (0 : Fin 1) G
    let K := SingleExpansion.family C (0 : Fin 1) H
    have components : ∀ e, FillingWitness T (F e) (K e) := by
      intro e
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      simpa only [F,K,SingleExpansion.selected] using w
    exact (expand C components).congr
      ((SingleExpansion.iso C (0 : Fin 1) G).trans (InterfacePermutation.PlugContext.iso a p G))
      ((SingleExpansion.iso C (0 : Fin 1) H).trans (InterfacePermutation.PlugContext.iso a p H))
end Hypernets.Copying.FillingWitness

namespace Hypernets.Copying.BoxPermutation
open Graph

/-- The reversed shallow pair is a genuine filling in a permuted outer context.
It is not incorrectly identified with the raw directed BPerm relation. -/
noncomputable def UpToIso.reverseWitness {d I O} {G H : Hypernet d I O}
    (rel : UpToIso G H) (free : FocusFree G) : FillingWitness template H G := by
  apply Classical.choice
  cases rel with
  | witness f step g =>
    have leftFree := (allLabels_iso_iff _ f).mp free
    cases step with
    | permute B p =>
      have bodyFree : FocusFree B := leftFree (0 : Fin 1)
      have inverse : template.Rel (box B) (right B p.symm) :=
        ⟨normalized B p.symm, fun _ => bodyFree⟩
      have w := (FillingWitness.of_rel 0 inverse).permuted p.outer.symm
      have iso := (InterfacePermutation.roundtrip
        (box (bound := _) (freeVariables := _) (InterfacePermutation.net B p.body.symm)) p.outer).symm
      exact ⟨w.congr g (iso.trans f.symm)⟩
end Hypernets.Copying.BoxPermutation
