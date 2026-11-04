import Hypernets.Copying.TermWeakening

/-! Arbitrary finite ambient environments for the two unchanged programs of
Proposition 12.2. These are actual Idem/BPullW calculations, not hypotheses
assuming translation correctness or an already proved final equivalence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph BoxPullWeakening

/-- Add the same unused resource to both endpoints of a calculation. -/
noncomputable def Calculation.extend {d I k h} {G H : Hypernet d I (environmentInterface k h)}
    (c : Calculation G H) (s : ShareSort) : Calculation (extend G s) (extend H s) :=
  (c.parallelRight (insertionBoundary I (List.replicate k .term) (List.replicate h .atom) s)
    (primitiveNet d (.weakening s))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).reboundary
      (List.append_nil I) (extended_interface s k h)

/-- Insert a finite variable block outside an otherwise unchanged graph. -/
def addVariables {d h} (G : Hypernet d [.term] (environmentInterface 0 h)) :
    (k : Nat) → Hypernet d [.term] (environmentInterface k h)
  | 0 => G
  | k+1 => extend (addVariables G k) .term

/-- Insert a finite atom block outside an otherwise unchanged graph. -/
def addAtoms {d k} (G : Hypernet d [.term] (environmentInterface k 0)) :
    (h : Nat) → Hypernet d [.term] (environmentInterface k h)
  | 0 => G
  | h+1 => extend (addAtoms G h) .atom

/-- A closed graph with explicit unused term and atom environment outputs. -/
def ambient {d} (G : Hypernet d [.term] []) (k h : Nat) :
    Hypernet d [.term] (environmentInterface k h) := addAtoms (addVariables G k) h

noncomputable def privateCell_step (k h : Nat) (s : ShareSort) :
    Calculation (Translation.privateCell (variables s k) (atoms s h))
      (extend (Translation.privateCell k h) s) := term_weakening (Term.privateCell k h) s

noncomputable def constantResult_step (k h : Nat) (s : ShareSort) :
    Calculation (Translation.constantResult (variables s k) (atoms s h))
      (extend (Translation.constantResult k h) s) := term_weakening (Term.constantResult k h) s

noncomputable def privateCell_variables (k : Nat) :
    Calculation (Translation.privateCell k 0) (addVariables (Translation.privateCell 0 0) k) := by
  induction k with
  | zero => exact .refl _ (Translation.term_focusFree _)
  | succ k ih => exact (privateCell_step k 0 .term).trans (ih.extend .term)

noncomputable def constantResult_variables (k : Nat) :
    Calculation (Translation.constantResult k 0) (addVariables (Translation.constantResult 0 0) k) := by
  induction k with
  | zero => exact .refl _ (Translation.term_focusFree _)
  | succ k ih => exact (constantResult_step k 0 .term).trans (ih.extend .term)

/-- The original reference-allocating program in every finite pair of environments
is structurally equivalent to its empty-environment graph with outside weakenings. -/
noncomputable def privateCell_environment (k h : Nat) :
    Calculation (Translation.privateCell k h) (ambient (Translation.privateCell 0 0) k h) := by
  induction h with
  | zero => exact privateCell_variables k
  | succ h ih => exact (privateCell_step k h .atom).trans (ih.extend .atom)

/-- The original constant-result program has the same finite-environment law. -/
noncomputable def constantResult_environment (k h : Nat) :
    Calculation (Translation.constantResult k h) (ambient (Translation.constantResult 0 0) k h) := by
  induction h with
  | zero => exact constantResult_variables k
  | succ h ih => exact (constantResult_step k h .atom).trans (ih.extend .atom)

/-- The named distinct-list boundary uses exactly the original list lengths. -/
noncomputable def privateCell_named {Name : Type} (E : Environment Name) :
    Calculation (Translation.privateCell E.variables.length E.atoms.length)
      (ambient (Translation.privateCell 0 0) E.variables.length E.atoms.length) :=
  privateCell_environment _ _

noncomputable def constantResult_named {Name : Type} (E : Environment Name) :
    Calculation (Translation.constantResult E.variables.length E.atoms.length)
      (ambient (Translation.constantResult 0 0) E.variables.length E.atoms.length) :=
  constantResult_environment _ _

/-- Arbitrary term weakening is sound in every admitted recursive observation
site, including sites inside boxes, with exact successful-run counts. -/
theorem term_weakening_addressed {k h e} (t : Term k h) (s : ShareSort)
    {C : Hypernet e [.term] []}
    (site : Site C (Translation.depth t) [.term] (environmentInterface (variables s k) (atoms s h)))
    (hostFree : FocusFree C)
    (closed : HoleFree (plugAt site
      (Translation.castDepth (Translation.depth_rename t (RetainedCopy.termResource s) (RetainedCopy.atomResource s))
        (Translation.term (Term.rename (RetainedCopy.termResource s) (RetainedCopy.atomResource s) t))))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Translation.castDepth
        (Translation.depth_rename t (RetainedCopy.termResource s) (RetainedCopy.atomResource s))
        (Translation.term (Term.rename (RetainedCopy.termResource s) (RetainedCopy.atomResource s) t))),(.search,.input 0)⟩
      ⟨e,plugAt site (extend (Translation.term t) s),(.search,.input 0)⟩ :=
  ((term_weakening t s).plugAt site hostFree).exact_equiv closed

/-- Exact observations for the original allocating program in any finite environment. -/
theorem privateCell_environment_addressed {k h e} {C : Hypernet e [.term] []}
    (site : Site C 3 [.term] (environmentInterface k h)) (hostFree : FocusFree C)
    (closed : HoleFree (plugAt site (Translation.privateCell k h))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Translation.privateCell k h),(.search,.input 0)⟩
      ⟨e,plugAt site (ambient (Translation.privateCell 0 0) k h),(.search,.input 0)⟩ :=
  ((privateCell_environment k h).plugAt site hostFree).exact_equiv closed

/-- Exact observations for the original constant-result program in any finite environment. -/
theorem constantResult_environment_addressed {k h e} {C : Hypernet e [.term] []}
    (site : Site C 2 [.term] (environmentInterface k h)) (hostFree : FocusFree C)
    (closed : HoleFree (plugAt site (Translation.constantResult k h))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Translation.constantResult k h),(.search,.input 0)⟩
      ⟨e,plugAt site (ambient (Translation.constantResult 0 0) k h),(.search,.input 0)⟩ :=
  ((constantResult_environment k h).plugAt site hostFree).exact_equiv closed
end Hypernets.Copying.Weakening
