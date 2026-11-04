import Hypernets.Copying.PropositionOperationalContexts

/-! Certified programs for the actual allocation and beta segment, including
all retained store edges. No semantic conclusion is assumed in these records. -/
namespace Hypernets.Copying.Proposition12_2
open Graph

theorem body_focusFree : FocusFree body := Translation.term_focusFree bodyTerm
theorem body_holeFree : HoleFree body := Translation.term_holeFree bodyTerm

theorem closure_focusFree : FocusFree (Application.closure body) :=
  Application.closure_labels _ _ body_focusFree (by intro m eq; cases eq)
theorem closure_holeFree : HoleFree (Application.closure body) :=
  Application.closure_labels _ _ body_holeFree (by intro h eq; cases eq)

theorem storeSuffix_labels (P : Primitive → Prop) (d : Nat)
    (weak : P (.weakening .atom)) (contr : P (.contraction .atom))
    (store : P .store) (one : P (.operation (.const (.nat 1)))) : AllLabels P (storeSuffix d) := by
  apply Serial.allLabels_net
  · apply Serial.allLabels_net
    · intro e; cases d
      all_goals
        change P (CanonicalTree.label .atom e)
        simp only [CanonicalTree.label]
        split
        · exact weak
        · exact contr
    · exact Translation.allLabels_primitive _ _ _ store
  · exact Translation.allLabels_primitive _ _ _ one

theorem storeSuffix_focusFree (d : Nat) : FocusFree (storeSuffix d) :=
  storeSuffix_labels _ d (by intro m eq; cases eq) (by intro m eq; cases eq)
    (by intro m eq; cases eq) (by intro m eq; cases eq)
theorem storeSuffix_holeFree (d : Nat) : HoleFree (storeSuffix d) :=
  storeSuffix_labels _ d (by intro h eq; cases eq) (by intro h eq; cases eq)
    (by intro h eq; cases eq) (by intro h eq; cases eq)

def referenceSource : OpenProgram 3 0 0 where
  graph := Allocation.before (numeral 3)
  focusFree := Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))
    (Stable.constant 3 (.nat 1)).focusFree
  holeFree := Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ (by intro h eq; cases eq))
    (Stable.constant 3 (.nat 1)).holeFree

def referenceTarget : OpenProgram 3 0 0 where
  graph := Allocation.after (numeral 3)
  focusFree := Allocation.after_focusFree _ (Stable.constant 3 (.nat 1)).focusFree
  holeFree := Allocation.after_holeFree _ (Stable.constant 3 (.nat 1)).holeFree

def betaLeft : OpenProgram 3 0 1 where
  graph := Application.before body (primitiveNet 3 .instanceEdge)
  focusFree := (Application.safe_sides body _ body_focusFree body_holeFree (Stable.instanceEdge 3)).1
  holeFree := (Application.safe_sides body _ body_focusFree body_holeFree (Stable.instanceEdge 3)).2.1

def betaRight : OpenProgram 3 0 1 where
  graph := Application.after body (primitiveNet 3 .instanceEdge)
  focusFree := (Application.safe_sides body _ body_focusFree body_holeFree (Stable.instanceEdge 3)).2.2.1
  holeFree := (Application.safe_sides body _ body_focusFree body_holeFree (Stable.instanceEdge 3)).2.2.2

def originalProgram : OpenProgram 3 0 0 where
  graph := Translation.privateCell 0 0
  focusFree := Translation.term_focusFree _
  holeFree := Translation.term_holeFree _

def allocatedProgram : OpenProgram 3 0 0 where
  graph := allocated
  focusFree := Application.before_labels _ body _ body_focusFree referenceTarget.focusFree
    (by intro m eq; cases eq) (by intro m eq; cases eq)
  holeFree := Application.before_labels _ body _ body_holeFree referenceTarget.holeFree
    (by intro h eq; cases eq) (by intro h eq; cases eq)

def betaSourceProgram : OpenProgram 3 0 0 where
  graph := betaSource
  focusFree := Serial.allLabels_net _ betaLeft.focusFree (storeSuffix_focusFree 3)
  holeFree := Serial.allLabels_net _ betaLeft.holeFree (storeSuffix_holeFree 3)

def openedProgram : OpenProgram 3 0 0 where
  graph := opened
  focusFree := Serial.allLabels_net _ betaRight.focusFree (storeSuffix_focusFree 3)
  holeFree := Serial.allLabels_net _ betaRight.holeFree (storeSuffix_holeFree 3)
end Hypernets.Copying.Proposition12_2
