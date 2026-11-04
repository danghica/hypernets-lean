import Hypernets.Copying.PropositionResultNormalization
import Hypernets.Copying.PaddingConstructors

/-! The result normalization at every adequate representation allowance.
Padding is applied to genuine structural certificates, not inferred from
determinism or assumed to preserve an arbitrary contextual equivalence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2.Result
open Graph

noncomputable def padWitness {T : PreTemplate} (closed : T.PaddingClosed)
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H)
    (N : Nat) (bound : d ≤ N) : FillingWitness T
      (Translation.padTo N bound G) (Translation.padTo N bound H) := by
  apply Classical.choice
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [Translation.padTo_add,Translation.padTo_add]
  exact ⟨w.pad closed n⟩

/-- The full schematic abstraction commutes with all extra depth allowances. -/
noncomputable def largeRight_padding (d : Nat) :
    DeepIso (Translation.padTo (d+2) (by omega) (Parametricity.largeRight 0))
      (Parametricity.largeRight d) := by
  induction d with
  | zero => rw [Translation.padTo_self]; exact DeepIso.refl _
  | succ d ih =>
    rw [Translation.padTo_succ _ (d+2) (by omega)]
    exact (Padding.congr ih).trans (Parametricity.largeRight_raise d)

def originalAt (d : Nat) : OpenProgram (d+2) 0 0 := original.padTo (d+2) (by omega)
def weakenedAt (d : Nat) : OpenProgram (d+2) 0 0 := weakened.padTo (d+2) (by omega)
def normalizedAt (d : Nat) : OpenProgram (d+2) 0 0 :=
  ⟨Parametricity.largeRight d,(Parametricity.labels_closed (Parametricity.largeRight_labels d)).1,
    (Parametricity.labels_closed (Parametricity.largeRight_labels d)).2⟩

noncomputable def program_witnessAt (d : Nat) : FillingWitness SharingTreeAlgebra.template
    (weakenedAt d).graph (normalizedAt d).graph :=
  (padWitness SharingTreeAlgebra.template_paddingClosed program_witness (d+2) (by omega)).congr
    (DeepIso.refl _) (largeRight_padding d)

/-- Exact-count normalization at every common allowance, including depth three
required by the original allocating program. The surrounding context may
have arbitrarily greater depth. -/
theorem original_normalizedAt_exact (d : Nat) :
    Combined.execution.Equiv CostOrder.exact (originalAt d) (normalizedAt d) := by
  have first : Combined.execution.Equiv CostOrder.exact (originalAt d) (weakenedAt d) :=
    (program_weakening.padTo (d+2) (by change 2 ≤ d+2; omega)).contextual_exact
  have second (C : ClosingContext (d+2) 0 0) :=
    SharingExecution.filling_exact_equiv SharingTreeAlgebra.template_sharingTrees
      SharingTreeAlgebra.template_paddingClosed ((program_witnessAt d).closing C)
        (C.fill_holeFree _ (weakenedAt d).holeFree) (C.fill_holeFree _ (normalizedAt d).holeFree)
  exact ⟨fun C => (first.1 C).trans (second C).1,fun C => (second C).2.trans (first.2 C)⟩

theorem original_normalizedAt (d : Nat) :
    Combined.execution.Equiv CostOrder.any (originalAt d) (normalizedAt d) :=
  ⟨fun C => (original_normalizedAt_exact d).1 C |>.mono (fun _ => trivial),
    fun C => (original_normalizedAt_exact d).2 C |>.mono (fun _ => trivial)⟩
end Hypernets.Copying.Proposition12_2.Result
