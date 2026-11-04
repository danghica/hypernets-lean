import Hypernets.Copying.PropositionResultEnvironments
import Hypernets.Copying.ParametricityFamilyBlocks

/-! The concrete single-closure private-cell instance used in Figure 22.
The full finite-family template is specialized through checked original
occurrences: zero-sized families remove no actual graph edge. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2.ParametricInstance
open Graph Parametricity

/-- A one-large, zero-small family is precisely its retained original member,
up to ordered recursive representation. Empty replication adds no edges. -/
noncomputable def singletonFamily_iso {d k}
    (A B : Hypernet d [.term] (List.replicate k .term)) :
    DeepIso A ((FamilyComponents.family A B 1 0).reboundary rfl (by simp)) := by
  apply ((FamilyComponents.large A B 1 0 0).reboundaryTarget rfl (by simp)).iso_of_edge_surjective
  · intro i
    have z : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst i
    rfl
  · intro i
    exact congrArg Port.output (Fin.ext rfl)
  · intro e
    rcases e with ⟨b,e⟩
    cases b
    · rcases e with ⟨b,e⟩
      cases b
      · exact ⟨e,rfl⟩
      · exact nomatch e
    · exact nomatch e

noncomputable def leftFamily_iso (d : Nat) :
    DeepIso (Parametricity.largeLeft d) (Parametricity.leftFamily d 1 0) :=
  by simpa only [Net.reboundary_refl,FamilyComponents.family,Parametricity.leftFamily,Parametricity.right,Parametricity.rightFamily] using
    singletonFamily_iso (k := 1) (Parametricity.largeLeft d) (Parametricity.smallLeft (d+1))

noncomputable def rightFamily_iso (d : Nat) :
    DeepIso (Parametricity.largeRight d) (Parametricity.right d 1 0) :=
  by simpa only [Net.reboundary_refl,FamilyComponents.family,Parametricity.leftFamily,Parametricity.right,Parametricity.rightFamily] using
    singletonFamily_iso (k := 0) (Parametricity.largeRight d) (Parametricity.smallRight (d+1))

/-- The normalized private closure retains any actual one-input term sharing
 tree; no canonicalization of that retained private tree is required. -/
def privateClosureWith (d : Nat) (C : ContractionTree .term 1) : Hypernet (d+2) [.term] [] :=
  Serial.net (Serial.net (Parametricity.largeLeft d) (C.atDepth (d+2)))
    (Parametricity.privateCell (d+2))

/-- The Figure 22 specialization retains the full canonical term and atom
 trees, single instance, store and numeral. No free x escapes. -/
def privateClosure (d : Nat) : Hypernet (d+2) [.term] [] :=
  privateClosureWith d (ContractionTree.canonical .term 1)

/-- The complete arbitrary-tree relation is an actual literal family instance. -/
theorem pairWith (d : Nat) (C : ContractionTree .term 1) :
    Parametricity.Pair (privateClosureWith d C) (Parametricity.largeRight d) :=
  .witness (Serial.congr (Serial.congr (leftFamily_iso d) (DeepIso.refl _)) (DeepIso.refl _))
    (.families (m₁ := 1) (m₂ := 0) d C) (rightFamily_iso d).symm

/-- This relation is the proved literal template instance, not a constructor
 asserting the desired observational equivalence. -/
theorem pair (d : Nat) : Parametricity.Pair (privateClosure d) (Parametricity.largeRight d) :=
  pairWith d (ContractionTree.canonical .term 1)

def privateProgram (d : Nat) : OpenProgram (d+2) 0 0 :=
  ⟨privateClosure d,(pair d).closed.1.1,(pair d).closed.1.2⟩

/-- Private-state elimination is a quantitative contextual improvement under
all original binding-free observations; callbacks need not terminate. -/
theorem improvement (d : Nat) : Combined.execution.Refines CostOrder.improvement
    (privateProgram d) (Result.normalizedAt d) :=
  Parametricity.pair_contextual_improvement _ _ (pair d)

/-- The converse has the original overhead bound, obtained before costs are
forgotten. It includes arbitrary duplication and garbage collection contexts. -/
theorem reverse_overhead (d : Nat) : Combined.execution.Refines CostOrder.overhead
    (Result.normalizedAt d) (privateProgram d) := by
  intro C
  exact Parametricity.filling_reverse_overhead
    ((FillingWitness.of_rel 0 (pair d)).closing C)
      (C.fill_holeFree _ (privateProgram d).holeFree)
      (C.fill_holeFree _ (Result.normalizedAt d).holeFree)

theorem equivalent (d : Nat) : Combined.execution.Equiv CostOrder.any
    (privateProgram d) (Result.normalizedAt d) :=
  Parametricity.pair_contextual_equiv _ _ (pair d)

/-- The complete final segment of Figure 22: from its normalized private-cell
closure to the actual unchanged constant-result translation. -/
theorem private_original (d : Nat) : Combined.execution.Equiv CostOrder.any
    (privateProgram d) (Result.originalAt d) :=
  Combined.execution.equiv_trans (equivalent d)
    ⟨(Result.original_normalizedAt d).2,(Result.original_normalizedAt d).1⟩

/-- Quantitative forward comparison survives the final exact structural
normalization; the original right program does not add successful-run cost. -/
theorem private_original_improvement (d : Nat) : Combined.execution.Refines CostOrder.improvement
    (privateProgram d) (Result.originalAt d) := by
  intro C
  exact (improvement d C).trans
    (((Result.original_normalizedAt_exact d).2 C).mono (by intro a b eq; cases eq; exact Nat.le_refl _))
end Hypernets.Copying.Proposition12_2.ParametricInstance
