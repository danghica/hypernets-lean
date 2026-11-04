import Hypernets.Copying.PropositionAllocationEquivalence
import Hypernets.Copying.AmbientWeakeningContext

/-! The allocation and beta segment for the unchanged proposition program in
every finite pair of environments. The final private-state elimination is
still a separate obligation; the intermediate is the actual opened graph. -/
namespace Hypernets.Copying.Proposition12_2
open Graph

def originalInEnvironment (k h : Nat) : OpenProgram 3 k h where
  graph := Translation.privateCell k h
  focusFree := Translation.term_focusFree _
  holeFree := Translation.term_holeFree _

def openedInEnvironment (k h : Nat) : OpenProgram 3 k h :=
  Weakening.ambientProgram openedProgram k h

/-- Exact-count boundary weakening is proved before costs are forgotten. -/
theorem environment_weakening_exact (k h : Nat) :
    Combined.execution.Equiv CostOrder.exact (originalInEnvironment k h)
      (Weakening.ambientProgram originalProgram k h) :=
  (Weakening.privateCell_environment k h).contextual_exact

/-- No free-environment restriction remains in the concrete allocation-and-beta link. -/
theorem original_opened_environment (k h : Nat) :
    Combined.execution.Equiv CostOrder.any (originalInEnvironment k h) (openedInEnvironment k h) := by
  have eq := environment_weakening_exact k h
  have forget : Combined.execution.Equiv CostOrder.any (originalInEnvironment k h)
      (Weakening.ambientProgram originalProgram k h) :=
    ⟨fun C => (eq.1 C).mono (fun _ => trivial),fun C => (eq.2 C).mono (fun _ => trivial)⟩
  exact Combined.execution.equiv_trans forget (Weakening.ambient_equiv _ _ original_opened k h)

/-- Named distinct-list environments supply their original ordered lengths. -/
theorem original_opened_named {Name : Type} (E : Environment Name) :
    Combined.execution.Equiv CostOrder.any
      (originalInEnvironment E.variables.length E.atoms.length)
      (openedInEnvironment E.variables.length E.atoms.length) :=
  original_opened_environment _ _

/-- Every original binding-free closing context observes the same termination
behaviour on both endpoints, including contexts with arbitrary callback use. -/
theorem original_opened_environment_termination {k h} (C : ClosingContext 3 k h) :
    Combined.execution.Terminates (C.close (originalInEnvironment k h)) ↔
      Combined.execution.Terminates (C.close (openedInEnvironment k h)) :=
  (Combined.execution.equiv_any_iff _ _).mp (original_opened_environment k h) C
end Hypernets.Copying.Proposition12_2
