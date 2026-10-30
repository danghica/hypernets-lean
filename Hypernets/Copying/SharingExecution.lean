import Hypernets.Copying.SharingTreeMatching
import Hypernets.Copying.SharingRooted

/-! Exact contextual and pointed execution consequences of the completed
sharing-template proof, at arbitrary recursive original observing sites. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace SharingExecution
variable {T : PreTemplate} (trees : T.SharingTrees) (padding : T.PaddingClosed)
include trees padding

/-- Sharing-tree paired fillings have exact quantitative equivalence, using proved
input safety and both proved robustness directions of the original machine. -/
theorem filling_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  have lifting := w.allContexts_initial_lifting trees.outputClosed left right
  exact ⟨Specimens.sufficiency T Specimens.allContexts trees.outputClosed CostOrder.reasonable_exact
      (trees.inputSafe padding _ _) (trees.robust padding _ _ _) lifting,
    Specimens.sufficiency_converse T Specimens.allContexts trees.outputClosed CostOrder.reasonable_exact
      (trees.inputSafe padding _ _) (trees.robust_converse padding _ _ _) lifting⟩

/-- Successful termination agrees at every exact transition count, including
contexts whose other computations may diverge or become stuck. -/
theorem filling_termination_count {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) := by
  have eq := filling_exact_equiv trees padding w left right
  constructor
  · rintro ⟨s,run,final⟩
    obtain ⟨m,t,cost,run',final'⟩ := eq.1 run final
    cases cost
    exact ⟨t,run',final'⟩
  · rintro ⟨t,run,final⟩
    obtain ⟨m,s,cost,run',final'⟩ := eq.2 run final
    cases cost
    exact ⟨s,run',final'⟩

/-- An actual template pair can be replaced at any original addressed site,
including under boxes, in every closed observing graph. No binding restriction
or bound on the surrounding depth is imposed. -/
theorem addressed_exact_equiv {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : T.Rel G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  filling_exact_equiv trees padding ((FillingWitness.of_rel 0 pair).plugAt site free) left right

/-- The addressed-context consequence preserves exact successful-transition
counts for each actual replacement, not merely termination after forgetting costs. -/
theorem addressed_termination_count {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : T.Rel G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,plugAt site G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,plugAt site H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) :=
  filling_termination_count trees padding ((FillingWitness.of_rel 0 pair).plugAt site free) left right n
/-- Sharing-tree structural changes preserve every successful transition count
from an arbitrary common host token. Input safety and both robustness
directions are the already proved concrete theorems. -/
theorem pointed_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,w.leftPosition q⟩ ⟨d,H,w.rightPosition q⟩ := by
  have lifting := w.allContexts_pointed_lifting trees.outputClosed left right q typed mode
    leftRooted rightRooted
  exact ⟨Specimens.sufficiency T Specimens.allContexts trees.outputClosed CostOrder.reasonable_exact
      (trees.inputSafe padding _ _) (trees.robust padding _ _ _) lifting,
    Specimens.sufficiency_converse T Specimens.allContexts trees.outputClosed CostOrder.reasonable_exact
      (trees.inputSafe padding _ _) (trees.robust_converse padding _ _ _) lifting⟩

/-- The same exact equivalence in the original representation quotient used
by quasi-specimens; no extra quotient or coarse observation is introduced. -/
theorem pointed_class_exact_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩)
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) := by
  have eq := pointed_exact_equiv trees padding w left right q typed mode leftRooted rightRooted
  exact ⟨(StateClass.refines_iff _ _ _).mpr eq.1,
    (StateClass.refines_iff _ _ _).mpr eq.2⟩

/-- Pointed execution agrees at each exact cost, with no termination premise
and no bound on the subsequent run or on the enclosing recursive graph. -/
theorem pointed_termination_count {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) (n : Nat) :
    (∃ s, unboundedMachine.Steps n ⟨d,G,w.leftPosition q⟩ s ∧ unboundedMachine.final s) ↔
    (∃ t, unboundedMachine.Steps n ⟨d,H,w.rightPosition q⟩ t ∧ unboundedMachine.final t) := by
  have eq := pointed_exact_equiv trees padding w left right q typed mode leftRooted rightRooted
  constructor
  · rintro ⟨s,run,final⟩
    obtain ⟨m,t,cost,run',final'⟩ := eq.1 run final
    cases cost
    exact ⟨t,run',final'⟩
  · rintro ⟨t,run,final⟩
    obtain ⟨m,s,cost,run',final'⟩ := eq.2 run final
    cases cost
    exact ⟨s,run',final'⟩

/-- A rooted actual left endpoint suffices for a pointed semantic correction:
the right root is obtained by exact reflection of the original search path. -/
theorem pointed_exact_equiv_of_left_rooted {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩)) :
    unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,w.leftPosition q⟩ ⟨d,H,w.rightPosition q⟩ :=
  pointed_exact_equiv trees padding w left right q typed mode leftRooted
    ((w.sharing_rooted_iff trees left right 0 q mode).mp leftRooted)

/-- The representation-quotient form for composing a completed sharing
template correction with an actual residual specimen. -/
theorem pointed_class_exact_equiv_of_left_rooted {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩)
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) :=
  pointed_class_exact_equiv trees padding w left right q typed mode leftRooted
    ((w.sharing_rooted_iff trees left right 0 q mode).mp leftRooted)

/-- A correction can instead start from a proved root on its actual right
endpoint; search reflection supplies the intermediate left root exactly. -/
theorem pointed_class_exact_equiv_of_right_rooted {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩)
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) :=
  pointed_class_exact_equiv trees padding w left right q typed mode
    ((w.sharing_rooted_iff trees left right 0 q mode).mpr rightRooted) rightRooted
end SharingExecution
end Hypernets.Copying
