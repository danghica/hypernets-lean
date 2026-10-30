import Hypernets.Copying.FullCopyingForwardRobustness
import Hypernets.Copying.CopyingTemplateConverseRobustness
import Hypernets.Copying.CopyingTemplateInputSafety
import Hypernets.Copying.AddressedWitness
import Hypernets.Copying.NullaryPointedExecution

/-! The full original copying template is a contextual improvement and
preserves successful termination. Its distinguished 2/0 input prefix is kept:
no exact-count equivalence is asserted for the copying relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined

/-- Arbitrarily many recursive original copying occurrences improve every
successful execution in every unrestricted common context. -/
theorem filling_improvement {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Refines CostOrder.improvement
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  Specimens.sufficiency template Specimens.allContexts template_outputClosed
    CostOrder.reasonable_improvement (template_inputSafe_improvement _)
    (template_robust _ _ _) (w.allContexts_initial_lifting template_outputClosed left right)

/-- The converse successful run has at least the right run's length. This
uses the proved converse robustness with its original converse-cost safety
condition, retaining the quantitative direction of the copying optimization. -/
theorem filling_reverse_overhead {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Refines CostOrder.overhead
      ⟨d,H,(.search,.input 0)⟩ ⟨d,G,(.search,.input 0)⟩ :=
  Specimens.sufficiency_converse template Specimens.allContexts template_outputClosed
    CostOrder.reasonable_overhead (template_inputSafe_improvement _)
    (template_robust_converse _ _ _) (w.allContexts_initial_lifting template_outputClosed left right)

/-- Costs are forgotten only after the forward and converse quantitative
comparisons have both been proved for the actual original machine. -/
theorem filling_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.any
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  ⟨(filling_improvement w left right).mono (fun _ => trivial),
    (filling_reverse_overhead w left right).mono (fun _ => trivial)⟩

/-- Actual successful termination agrees without any premise that a callback
or enclosing computation terminates, and with stuckness kept distinct. -/
theorem filling_termination {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H) :
    (∃ n s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ m t, unboundedMachine.Steps m ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) := by
  have eq := filling_equiv w left right
  constructor
  · rintro ⟨n,s,run,final⟩
    obtain ⟨m,t,_,run',final'⟩ := eq.1 run final
    exact ⟨m,t,run',final'⟩
  · rintro ⟨m,t,run,final⟩
    obtain ⟨n,s,_,run',final'⟩ := eq.2 run final
    exact ⟨n,s,run',final'⟩

/-- The literal copying pair may be replaced at any original addressed site,
including inside boxes, in every closed unrestricted observing graph. -/
theorem addressed_improvement {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : Pair G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Refines CostOrder.improvement
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  filling_improvement ((FillingWitness.of_rel 0 pair).plugAt site free) left right

/-- The same arbitrary-depth addressed replacements preserve termination in
both directions; the observing context need not be binding-free. -/
theorem addressed_equiv {d} {C : Hypernet d [.term] []} {r I O}
    (site : Site C r I O) (free : FocusFree C) {G H : Hypernet r I O}
    (pair : Pair G H) (left : HoleFree (plugAt site G)) (right : HoleFree (plugAt site H)) :
    unboundedMachine.Equiv CostOrder.any
      ⟨d,plugAt site G,(.search,.input 0)⟩ ⟨d,plugAt site H,(.search,.input 0)⟩ :=
  filling_equiv ((FillingWitness.of_rel 0 pair).plugAt site free) left right

/-- The actual paired residual at any common host token has the same directed
improvement. Both original roots are the normal specimen applicability
conditions, and the token is not already requesting a rewrite. -/
theorem pointed_improvement {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    unboundedMachine.Refines CostOrder.improvement
      ⟨d,G,w.leftPosition q⟩ ⟨d,H,w.rightPosition q⟩ :=
  Specimens.sufficiency template Specimens.allContexts template_outputClosed
    CostOrder.reasonable_improvement (template_inputSafe_improvement _) (template_robust _ _ _)
    (w.allContexts_pointed_lifting template_outputClosed left right q typed mode leftRooted rightRooted)

/-- At the same actual common point, converse robustness supplies the original
reverse cost inequality rather than an incorrect exact-count equivalence. -/
theorem pointed_reverse_overhead {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    unboundedMachine.Refines CostOrder.overhead
      ⟨d,H,w.rightPosition q⟩ ⟨d,G,w.leftPosition q⟩ :=
  Specimens.sufficiency_converse template Specimens.allContexts template_outputClosed
    CostOrder.reasonable_overhead (template_inputSafe_improvement _) (template_robust_converse _ _ _)
    (w.allContexts_pointed_lifting template_outputClosed left right q typed mode leftRooted rightRooted)

/-- Pointed termination equivalence follows by forgetting costs only after
both inequalities, and is available for actual residual compensation. -/
theorem pointed_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    unboundedMachine.Equiv CostOrder.any
      ⟨d,G,w.leftPosition q⟩ ⟨d,H,w.rightPosition q⟩ :=
  ⟨(pointed_improvement w left right q typed mode leftRooted rightRooted).mono (fun _ => trivial),
    (pointed_reverse_overhead w left right q typed mode leftRooted rightRooted).mono (fun _ => trivial)⟩

/-- The original representation quotient receives the same pointed
termination equivalence; no additional observation relation is introduced. -/
theorem pointed_class_equiv {d} {G H : Hypernet d [.term] []}
    (w : FillingWitness template G H) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite)
    (leftRooted : StateClass.Rooted (StateClass.ofState ⟨d,G,w.leftPosition q⟩))
    (rightRooted : StateClass.Rooted (StateClass.ofState ⟨d,H,w.rightPosition q⟩)) :
    StateClass.machine.Equiv CostOrder.any
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩)
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) := by
  have eq := pointed_equiv w left right q typed mode leftRooted rightRooted
  exact ⟨(StateClass.refines_iff _ _ _).mpr eq.1,(StateClass.refines_iff _ _ _).mpr eq.2⟩

/-- The same theorem specializes to every original binding-free observation
of open program graphs at arbitrary variable and atom environments. -/
theorem pair_contextual_improvement {d k h} (G H : OpenProgram d k h)
    (pair : Pair G.graph H.graph) : Combined.execution.Refines CostOrder.improvement G H := by
  intro C
  exact filling_improvement ((FillingWitness.of_rel 0 pair).closing C)
    (C.fill_holeFree G.graph G.holeFree) (C.fill_holeFree H.graph H.holeFree)

/-- Copying preserves the paper's termination observations in both directions
for all original closing contexts of the actual open graph interfaces. -/
theorem pair_contextual_equiv {d k h} (G H : OpenProgram d k h)
    (pair : Pair G.graph H.graph) : Combined.execution.Equiv CostOrder.any G H := by
  constructor
  · intro C
    exact (pair_contextual_improvement G H pair C).mono (fun _ => trivial)
  · intro C
    exact (filling_reverse_overhead ((FillingWitness.of_rel 0 pair).closing C)
      (C.fill_holeFree G.graph G.holeFree) (C.fill_holeFree H.graph H.holeFree)).mono (fun _ => trivial)

end Hypernets.Copying.CopyingTemplate
