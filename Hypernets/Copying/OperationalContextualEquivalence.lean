import Hypernets.Copying.FullOperationalConverseRobustness
import Hypernets.Copying.ContextualRobustness

/-! The proved operational templates give contextual improvement and
termination equivalence for the original copying machine and every original
binding-free closing context. No safety or robustness premise remains. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace FillingWitness
/-- A closed recursively filled pair with an admissible actual common context
supplies its own initial lifting, including rootedness of both machine states. -/
theorem binding_initial_lifting {T : PreTemplate} (closed : T.OutputClosed)
    {d} {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (left : HoleFree G) (right : HoleFree H) :
    (Specimens.system T Specimens.bindingFreeContexts closed).Lifting
      (StateClass.ofState ⟨d,G,(.search,.input 0)⟩)
      (StateClass.ofState ⟨d,H,(.search,.input 0)⟩) := by
  let S := w.bindingSpecimen binding left right (.search,.input 0) rfl
  have l := w.bindingSpecimen_left binding left right (.search,.input 0) rfl
  have r := w.bindingSpecimen_right binding left right (.search,.input 0) rfl
  refine ⟨S,.inl (by change Focus.search ≠ Focus.rewrite; decide),?_,?_,l.symm,r.symm⟩
  · change StateClass.Rooted (StateClass.ofState S.leftState)
    rw [l]
    exact Search.rooted_initial G 0
  · change StateClass.Rooted (StateClass.ofState S.rightState)
    rw [r]
    exact Search.rooted_initial H 0
end FillingWitness

namespace OperationalTemplates
/-- Micro-beta and reference creation are improvements in every original
binding-free closing context, with no bound on the context's surrounding depth. -/
theorem pair_contextual_improvement {kind d k h} (G H : OpenProgram d k h)
    (pair : Pair kind G.graph H.graph) :
    Combined.execution.Refines CostOrder.improvement G H :=
  Specimens.contextual_refines (template kind) (template_outputClosed kind)
    CostOrder.reasonable_improvement (template_bindingFree_inputSafe_improvement kind _)
    (template_robust kind _ _ _) G H pair

/-- Both original operational families preserve successful termination in all
binding-free observations. Costs are forgotten only at this final application. -/
theorem pair_contextual_equiv {kind d k h} (G H : OpenProgram d k h)
    (pair : Pair kind G.graph H.graph) :
    Combined.execution.Equiv CostOrder.any G H :=
  Specimens.contextual_equiv (template kind) (template_outputClosed kind)
    CostOrder.reasonable_termination (template_bindingFree_inputSafe kind _)
    (template_bindingFree_inputSafe kind _) (template_robust kind _ _ _)
    (template_robust_converse kind _ _ _) G H pair

/-- The contextual theorem states equivalence of actual successful observations,
including when either surrounding computation diverges or becomes stuck. -/
theorem pair_contextual_termination {kind d k h} (G H : OpenProgram d k h)
    (pair : Pair kind G.graph H.graph) (C : ClosingContext d k h) :
    Combined.execution.Terminates (C.close G) ↔ Combined.execution.Terminates (C.close H) :=
  (Combined.execution.equiv_any_iff G H).mp (pair_contextual_equiv G H pair) C

/-- Arbitrarily many recursive operational occurrences in one binding-free
common context preserve the directed non-increasing-cost comparison. -/
theorem filling_improvement {kind d} {G H : Hypernet d [.term] []}
    (w : FillingWitness (template kind) G H) (binding : BindingFree w.context)
    (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Refines CostOrder.improvement
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ :=
  Specimens.sufficiency (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)
    CostOrder.reasonable_improvement (template_bindingFree_inputSafe_improvement kind _)
    (template_robust kind _ _ _) (w.binding_initial_lifting (template_outputClosed kind) binding left right)

/-- All actual recursive fillings of either operational template are equivalent
for termination, without assuming any run terminates or every filling is shallow. -/
theorem filling_equiv {kind d} {G H : Hypernet d [.term] []}
    (w : FillingWitness (template kind) G H) (binding : BindingFree w.context)
    (left : HoleFree G) (right : HoleFree H) :
    unboundedMachine.Equiv CostOrder.any
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  have lifting := w.binding_initial_lifting (template_outputClosed kind) binding left right
  exact ⟨Specimens.sufficiency (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)
      CostOrder.reasonable_termination (template_bindingFree_inputSafe kind _)
      (template_robust kind _ _ _) lifting,
    Specimens.sufficiency_converse (template kind) Specimens.bindingFreeContexts (template_outputClosed kind)
      CostOrder.reasonable_termination (template_bindingFree_inputSafe kind _)
      (template_robust_converse kind _ _ _) lifting⟩

/-- Successful finite runs correspond with possibly different transition counts;
the operational template's search and compute prefix is not declared cost-free. -/
theorem filling_termination {kind d} {G H : Hypernet d [.term] []}
    (w : FillingWitness (template kind) G H) (binding : BindingFree w.context)
    (left : HoleFree G) (right : HoleFree H) :
    (∃ n s, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ s ∧ unboundedMachine.final s) ↔
    (∃ m t, unboundedMachine.Steps m ⟨d,H,(.search,.input 0)⟩ t ∧ unboundedMachine.final t) := by
  have eq := filling_equiv w binding left right
  constructor
  · rintro ⟨n,s,run,final⟩
    obtain ⟨m,t,_,run',final'⟩ := eq.1 run final
    exact ⟨m,t,run',final'⟩
  · rintro ⟨m,t,run,final⟩
    obtain ⟨n,s,_,run',final'⟩ := eq.2 run final
    exact ⟨n,s,run',final'⟩
end OperationalTemplates
end Hypernets.Copying
