import Hypernets.Copying.PropositionSourceNormalization
import Hypernets.Copying.PropositionPrefixPadding
import Hypernets.Copying.PropositionFinalSegment

/-! Proposition 12.2 for the original terms and full binding-free graph
observations, at every common adequate allowance and in every environment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2
open Graph

/-- The actual normalized private graph, including its store, commutes with
an extra allowance through proved constructor isomorphisms. -/
noncomputable def private_raise (d : Nat) : DeepIso
    (raise (d+2) (ParametricInstance.privateClosure d))
    (ParametricInstance.privateClosure (d+1)) :=
  (Padding.serial _ _).trans
    (Serial.congr (Source.normalized_raise d) (Parametricity.privateCell_raise (d+2)))

noncomputable def private_padding (d : Nat) : DeepIso
    (Translation.padTo (d+3) (by omega) (ParametricInstance.privateClosure 1))
    (ParametricInstance.privateClosure (d+1)) := by
  induction d with
  | zero => rw [Translation.padTo_self]; exact DeepIso.refl _
  | succ d ih =>
    rw [Translation.padTo_succ _ (d+3) (by omega)]
    exact (Padding.congr ih).trans (private_raise (d+1))

/-- Full source normalization preserves exact successful-run counts at every
adequate depth and in arbitrary binding-free observations. -/
theorem opened_private_exact (d : Nat) : Combined.execution.Equiv CostOrder.exact
    (openedProgram.padTo (d+3) (by omega)) (ParametricInstance.privateProgram (d+1)) := by
  have c := Source.openedCalculation.padTo (d+3) (by change 3 ≤ d+3; omega)
  exact (c.trans (.iso (private_padding d) c.focusFree.2)).contextual_exact

/-- The complete closed original-left to normalized-private prefix. -/
theorem original_private (d : Nat) : Combined.execution.Equiv CostOrder.any
    (originalProgram.padTo (d+3) (by omega)) (ParametricInstance.privateProgram (d+1)) := by
  have eq := opened_private_exact d
  exact Combined.execution.equiv_trans (original_opened_padTo (d+3) (by omega))
    ⟨fun C => (eq.1 C).mono (fun _ => trivial),fun C => (eq.2 C).mono (fun _ => trivial)⟩

/-- The unchanged allocating translation in a caller's common allowance. -/
def originalEnvironment (d k h : Nat) : OpenProgram (d+3) k h :=
  translatedProgram (Term.privateCell k h) (d+3) (by change 3 ≤ d+3; omega)

/-- Semantic weakening of the original left term is transported through its
actual calculation, including every original term and atom distributor. -/
theorem source_environment_exact (d k h : Nat) : Combined.execution.Equiv CostOrder.exact
    (originalEnvironment d k h)
    (Weakening.ambientProgram (originalProgram.padTo (d+3) (by omega)) k h) := by
  have c := (Weakening.privateCell_environment k h).padTo (d+3) (by change 3 ≤ d+3; omega)
  rw [Result.ambient_padTo] at c
  exact c.contextual_exact

/-- Compose weakening, allocation, beta, structural normalization,
parametricity and the exact right-hand normalization. No operational,
robustness, translation or termination hypothesis remains. -/
theorem equivalence_at (d k h : Nat) : Combined.execution.Equiv CostOrder.any
    (originalEnvironment d k h) (Result.originalEnvironment (d+1) k h) := by
  have first := source_environment_exact d k h
  have weakening : Combined.execution.Equiv CostOrder.any
      (originalEnvironment d k h)
      (Weakening.ambientProgram (originalProgram.padTo (d+3) (by omega)) k h) :=
    ⟨fun C => (first.1 C).mono (fun _ => trivial),fun C => (first.2 C).mono (fun _ => trivial)⟩
  exact Combined.execution.equiv_trans weakening
    (Combined.execution.equiv_trans
      (Weakening.ambient_equiv _ _ (original_private d) k h)
      (ParametricInstance.private_original_environment (d+1) k h))

end Hypernets.Copying.Proposition12_2

namespace Hypernets.Copying.Examples

/-- The literal Proposition 12.2 terms are observationally equivalent in the
complete copying UAM, for every finite pair of scoped environments. -/
theorem proposition12_2_scoped (k h : Nat) :
    ObservationalEquiv Combined.execution (Term.privateCell k h) (Term.constantResult k h) := by
  intro N left right
  have lower : 3 ≤ N := left
  obtain ⟨d,eq⟩ := Nat.exists_eq_add_of_le lower
  have eq' : N = d+3 := by omega
  clear eq
  subst N
  exact Proposition12_2.equivalence_at d k h

/-- Proposition 12.2 as printed: arbitrary finite distinct-list variable and
atom environments, the unchanged let/ref/lambda terms, and all binding-free
closing graph contexts at every adequate common representation allowance. -/
theorem proposition12_2 {Name : Type} (Γ Δ : List Name)
    (_variablesDistinct : Γ.Nodup) (_atomsDistinct : Δ.Nodup) :
    ObservationalEquiv Combined.execution
      (Term.privateCell Γ.length Δ.length) (Term.constantResult Γ.length Δ.length) :=
  proposition12_2_scoped _ _

/-- The same statement consumes the existing named-environment record. -/
theorem proposition12_2_environment {Name : Type} (E : Environment Name) :
    ObservationalEquiv Combined.execution
      (Term.privateCell E.variables.length E.atoms.length)
      (Term.constantResult E.variables.length E.atoms.length) :=
  proposition12_2 _ _ E.variables_distinct E.atoms_distinct

end Hypernets.Copying.Examples
