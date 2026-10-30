import Hypernets.Copying.NullaryExecution
import Hypernets.Copying.NullaryRooted

/-! Exact execution equivalence for nullary fillings at their actual common
host focus. The focus may be internal, and every endpoint rootedness premise
refers to the actual original unbounded machine state. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- A genuine recursive filling yields the actual pointed lifting when both
supplied endpoints are rooted. This does not reset an internal token to the
whole graph's input or assume rootedness of an unrelated state. -/
theorem FillingWitness.allContexts_pointed_lifting {T : PreTemplate} (closed : T.OutputClosed)
    {d} {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) (q : Search.Position w.context)
    (typed : w.context.vertexLabel q.2 = .term) (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    (Specimens.system T Specimens.allContexts closed).Lifting
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩)
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) := by
  obtain ⟨S,nonrewrite,lroot,rroot,l,r⟩ :=
    w.quasi closed left right q typed mode leftRooted rightRooted
  exact ⟨S,.inl nonrewrite,lroot,rroot,l,r.symm⟩

namespace NullaryExecution
variable {T : PreTemplate} (none : T.NoInputs) (padding : T.PaddingClosed)
include none padding

/-- Nullary structural changes preserve every successful transition count
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
  have lifting := w.allContexts_pointed_lifting none.outputClosed left right q typed mode
    leftRooted rightRooted
  exact ⟨Specimens.sufficiency T Specimens.allContexts none.outputClosed CostOrder.reasonable_exact
      (none.inputSafe _ _ _) (none.robust padding _ _ _) lifting,
    Specimens.sufficiency_converse T Specimens.allContexts none.outputClosed CostOrder.reasonable_exact
      (none.inputSafe _ _ _) (none.robust_converse padding _ _ _) lifting⟩

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
  have eq := pointed_exact_equiv none padding w left right q typed mode leftRooted rightRooted
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
  have eq := pointed_exact_equiv none padding w left right q typed mode leftRooted rightRooted
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
  pointed_exact_equiv none padding w left right q typed mode leftRooted
    ((w.nullary_rooted_iff none left 0 q).mp leftRooted)

/-- The representation-quotient form for composing a completed nullary
template correction with an actual residual specimen. -/
theorem pointed_class_exact_equiv_of_left_rooted {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness T G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩)
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) :=
  pointed_class_exact_equiv none padding w left right q typed mode leftRooted
    ((w.nullary_rooted_iff none left 0 q).mp leftRooted)

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
  pointed_class_exact_equiv none padding w left right q typed mode
    ((w.nullary_rooted_iff none left 0 q).mpr rightRooted) rightRooted
end NullaryExecution
end Hypernets.Copying
