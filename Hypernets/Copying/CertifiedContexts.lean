import Hypernets.Copying.SingleHoleTranslation
import Hypernets.Copying.ContextCongruence

/-! Actual translated graph contexts with proved occurrence and path certificates.
The remaining bridge to term congruence is the addressed filling law. -/
namespace Hypernets.Copying.ContextTranslation

/-- The existing translated graph, now packaged with an actual certified hole
address. Choosing an address changes neither its graph nor its interface. -/
noncomputable def certified {v a k b} (C : TermContext v a k b) (d name : Nat) :
    (r : Nat) × GraphContext r v a (graph C d name).1 k b := by
  let r := Classical.choose (SingleHole.context_certificate C d name)
  let s := Classical.choose (Classical.choose_spec (SingleHole.context_certificate C d name))
  have properties := Classical.choose_spec
    (Classical.choose_spec (SingleHole.context_certificate C d name))
  exact ⟨r,⟨(graph C d name).2,s,properties.1,properties.2⟩⟩

theorem certified_graph {v a k b} (C : TermContext v a k b) (d name : Nat) :
    (certified C d name).2.graph = (graph C d name).2 := rfl

/-- Graph-level congruence for the actual translated context. This compares
filled graphs; identifying those graphs with translated term fillings is a
separate theorem and is deliberately not built into the statement. -/
theorem certified_graph_congruence {State : Type u} (E : Execution State)
    (invariant : E.RespectsIso) {v a k b} (C : TermContext v a k b) (d name : Nat)
    {G H : OpenProgram (certified C d name).1 v a}
    (rel : E.Equiv CostOrder.any G H) :
    E.Equiv CostOrder.any ((certified C d name).2.fill G) ((certified C d name).2.fill H) :=
  E.equiv_context invariant _ rel
end Hypernets.Copying.ContextTranslation
