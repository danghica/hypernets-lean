import Hypernets.Copying.AtomicWeakeningOutputs

/-! All atomic semantic weakening base cases for the original Figure 16
translation. The witnesses are actual boundary-fixing graph isomorphisms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (termResource atomResource termResource_injective atomResource_injective)

noncomputable def variable_iso (d : Nat) {k} (h : Nat) (i : Fin k) (s : ShareSort) :
    DeepIso (extend (Translation.variableTerm d h i) s)
      (Translation.variableTerm d (atoms s h) (termResource s i)) := by
  apply (Atomic.variableComplement d h i s).extensionIso
  · intro v; rw [Atomic.variableComplement_old]; exact Atomic.variable_input _ _ _ _ i v
  · intro v; rw [Atomic.variableComplement_old]
    exact Atomic.environment_output _ (Atomic.variable_term _ _ _ _ i) (Atomic.variable_atom _ _ _ _ i) v
  · exact Atomic.variableComplement_output d h i s

noncomputable def atom_iso (d k : Nat) {h} (a : Fin h) (s : ShareSort) :
    DeepIso (extend (Translation.atom d k a) s)
      (Translation.atom d (variables s k) (atomResource s a)) := by
  apply (Atomic.atomComplement d k a s).extensionIso
  · intro v; rw [Atomic.atomComplement_old]; exact Atomic.atom_input _ _ _ _ a v
  · intro v; rw [Atomic.atomComplement_old]
    exact Atomic.environment_output _ (Atomic.atom_term _ _ _ _ a) (Atomic.atom_atom _ _ _ _ a) v
  · exact Atomic.atomComplement_output d k a s

noncomputable def constant_iso (d k h : Nat) (c : Constant) (s : ShareSort) :
    DeepIso (extend (Translation.constant d k h c) s)
      (Translation.constant d (variables s k) (atoms s h) c) := by
  apply (Atomic.constantComplement d k h c s).extensionIso
  · intro v; rw [Atomic.constantComplement_old]; exact Atomic.constant_input _ _ _ _ c v
  · intro v; rw [Atomic.constantComplement_old]
    exact Atomic.environment_output _ (Atomic.constant_term _ _ _ _ c) (Atomic.constant_atom _ _ _ _ c) v
  · exact Atomic.constantComplement_output d k h c s

/-- The variable base case retains the canonical selected contraction. -/
noncomputable def variable_extend (d : Nat) {k} (h : Nat) (i : Fin k) (s : ShareSort) :
    Calculation (Translation.variableTerm d (atoms s h) (termResource s i))
      (extend (Translation.variableTerm d h i) s) :=
  .iso (variable_iso d h i s).symm (Translation.language_focusFree (Translation.variable_language _ _ _))

/-- The atom base case retains the original instance edge and selected row. -/
noncomputable def atom_extend (d k : Nat) {h} (a : Fin h) (s : ShareSort) :
    Calculation (Translation.atom d (variables s k) (atomResource s a))
      (extend (Translation.atom d k a) s) :=
  .iso (atom_iso d k a s).symm (Translation.language_focusFree (Translation.atom_language _ _ _))

/-- All constants retain every original ambient weakening. -/
noncomputable def constant_extend (d k h : Nat) (c : Constant) (s : ShareSort) :
    Calculation (Translation.constant d (variables s k) (atoms s h) c)
      (extend (Translation.constant d k h c) s) :=
  .iso (constant_iso d k h c s).symm (Translation.language_focusFree (Translation.constant_language _ _ _ _))
end Hypernets.Copying.Weakening
