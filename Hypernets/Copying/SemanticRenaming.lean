import Hypernets.Copying.ContextualDerivation
import Hypernets.Copying.SemanticRenamingPadding

/-! Full-syntax bijective renaming is sound for the original copying machine
and observation contexts. The explicit inverse boundary action keeps the same
free resources connected to the same original context ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Change only external output positions of an admissible open graph. -/
def OpenProgram.permute {d k h} (G : OpenProgram d k h)
    (p : TypedPermutation (environmentInterface k h)) : OpenProgram d k h where
  graph := InterfacePermutation.net G.graph p
  focusFree := G.focusFree
  holeFree := G.holeFree

/-- The unchanged renamed translation, with its free-resource boundary action
undone. This is an explicit wiring operation outside the translated graph. -/
def renamedProgram {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (d : Nat) (bound : Translation.depth t ≤ d) : OpenProgram d k h :=
  (translatedProgram (Term.rename ρ.toFun α.toFun t) d
    (by rw [Translation.depth_rename]; exact bound)).permute
      (TypedPermutation.environment ρ α).symm

/-- Full Figure 16 translation respects bijective variable and atom renaming
in every original closing graph context, with exact successful-transition cost. -/
theorem Translation.term_rename_contextual_exact {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (d : Nat) (bound : depth t ≤ d) :
    Combined.execution.Equiv CostOrder.exact (translatedProgram t d bound)
      (renamedProgram t ρ α d bound) :=
  (padded_term_rename_derivation t ρ α d bound).contextual_exact

/-- Successful observations correspond at each finite count, including when
the context contains arbitrary effects, repeated uses, or divergent callbacks. -/
theorem Translation.term_rename_contextual_count {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (d : Nat) (bound : depth t ≤ d) (C : ClosingContext d k h) (n : Nat) :
    (∃ a, Combined.unboundedMachine.Steps n
      (Combined.execution.initial (C.close (translatedProgram t d bound))) a ∧
        Combined.unboundedMachine.final a) ↔
    (∃ b, Combined.unboundedMachine.Steps n
      (Combined.execution.initial (C.close (renamedProgram t ρ α d bound))) b ∧
        Combined.unboundedMachine.final b) :=
  (padded_term_rename_derivation t ρ α d bound).contextual_count C n

/-- Forgetting costs gives termination equivalence of the original translation
and the compensated renaming, at every sufficient representation allowance. -/
theorem Translation.term_rename_contextual_termination {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (d : Nat) (bound : depth t ≤ d) :
    Combined.execution.Equiv CostOrder.any (translatedProgram t d bound)
      (renamedProgram t ρ α d bound) :=
  (padded_term_rename_derivation t ρ α d bound).contextual_termination

/-- Named distinct-list environments expose precisely the same general result;
neither environment is required to be empty. -/
theorem Translation.named_rename_contextual_exact {Name : Type} (E : Environment Name)
    (t : Term E.variables.length E.atoms.length)
    (ρ : Bijection (Fin E.variables.length) (Fin E.variables.length))
    (α : Bijection (Fin E.atoms.length) (Fin E.atoms.length))
    (d : Nat) (bound : depth t ≤ d) :
    Combined.execution.Equiv CostOrder.exact (translatedProgram t d bound)
      (renamedProgram t ρ α d bound) := term_rename_contextual_exact t ρ α d bound

end Hypernets.Copying
