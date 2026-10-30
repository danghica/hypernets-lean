import Hypernets.Copying.ParametricityCopyNormalization
import Hypernets.Copying.ParametricityClosedCopyPair

/-! Identify the actual zero/one-private-resource copying distributions.
Only empty representation carriers disappear: the nonempty private row remains
the full original canonical D1,2, including its weakening. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyDistributors
open Graph Opening

noncomputable def privateRow (d : Nat) :
    DeepIso (CanonicalTree.atDepth .term 2 d) (Translation.environmentDistributor d 1 0 2) := by
  let f : Occurrence (CanonicalTree.atDepth .term 2 d) (Translation.environmentDistributor d 1 0 2) :=
    CopyingDouble.Components.resource (k := 1) (h := 0) (0 : Fin 1)
  apply f.iso_of_edge_surjective
  · intro i
    change Fin 2 at i
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with rfl | rfl
    · exact CopyingDouble.Components.resource_input (k := 1) (h := 0) (0 : Fin 1) false
    · exact CopyingDouble.Components.resource_input (k := 1) (h := 0) (0 : Fin 1) true
  · intro i
    change Fin 1 at i
    have zero : i=0 := Subsingleton.elim _ _; subst i
    exact CopyingDouble.Components.resource_output (k := 1) (h := 0) (0 : Fin 1)
  · intro e
    obtain ⟨i,x,eq⟩ := CopyingDouble.Components.resource_cover (k := 1) (h := 0) e
    change Fin 1 at i
    have zero : i=0 := Subsingleton.elim _ _; subst i
    exact ⟨x,eq⟩

noncomputable def privatePair {d} (H : Hypernet d [.term] (environmentInterface 1 0)) :
    DeepIso (Net.Tensor.net H H) (CopyingMerge.pair (a := 1) (b := 1) H H) := by
  let f := Occurrence.ParallelJoin.occurrence (Net.Tensor.family H H)
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro side; cases side <;> simp⟩
    (CopyingMerge.pairComponent (a := 1) (b := 1) H H)
    (by intro side other ne e x eq; exact ne (congrArg Sigma.fst eq))
  apply f.iso_of_edge_surjective
  · intro i
    change Fin 2 at i
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with rfl | rfl <;> rfl
  · intro i
    change Fin 2 at i
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with rfl | rfl <;> rfl
  · intro e; exact ⟨e,rfl⟩

/-- The private lambda's copy merge is exactly two original lambdas followed
by the complete canonical two-input term tree. -/
noncomputable def privateMerge {d} (H : Hypernet d [.term] (environmentInterface 1 0)) :
    DeepIso (Serial.net (Net.Tensor.net H H) (CanonicalTree.atDepth .term 2 d))
      (CopyingMerge.net (a := 1) (b := 1) H H) :=
  Serial.congr (privatePair H) (privateRow d)

/-- A closed lambda has no resource rows: the literal empty distributor
contributes no edge and the two ordered payloads remain unchanged. -/
noncomputable def closedMerge {d} (H : Hypernet d [.term] (environmentInterface 0 0)) :
    DeepIso (Net.Tensor.net H H) (CopyingMerge.net (a := 1) (b := 1) H H) :=
  ClosedCopyPair.iso H

end Hypernets.Copying.Parametricity.CopyDistributors
