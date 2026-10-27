import Hypernets.Copying.AddressedFillings

/-! Robustness for every original binding-free closing observation. -/
namespace Hypernets.Copying
open Graph Combined

namespace Combined.StateClass
/-- Whole-graph recursive isomorphism identifies the actual initial states;
there is no computation or cost attached to this change of carrier names. -/
theorem initial_iso {d} {G H : Hypernet d [.term] []} (f : DeepIso G H) :
    ofState ⟨d,G,(.search,.input 0)⟩ = ofState ⟨d,H,(.search,.input 0)⟩ :=
  Quotient.sound (.iso (.lift ⟨f,rfl,rfl⟩))
end Combined.StateClass

namespace Specimens
/-- The context class used by the original observation definition. -/
def bindingFreeContexts (d : Nat) (C : Hypernet d [.term] []) : Prop := BindingFree C

variable (T : PreTemplate) (closed : T.OutputClosed)

/-- Every original addressed closing context supplies a rooted remote lifting
witness for its actual fillings. In particular, certificates are conclusions,
not extra restrictions on which observations may be made. -/
theorem closing_initial_lifting {d k h} (C : ClosingContext d k h)
    (G H : OpenProgram d k h) (rel : T.Rel G.graph H.graph) :
    (system T bindingFreeContexts closed).Lifting
      (StateClass.execution.initial (C.close G)) (StateClass.execution.initial (C.close H)) := by
  obtain ⟨L,R,pair,lc,rc,⟨li⟩,⟨ri⟩⟩ := AddressedFillings.closing T C G H rel
  change (system T bindingFreeContexts closed).Lifting
    (StateClass.ofState ⟨C.depth,C.fill G.graph,(.search,.input 0)⟩)
    (StateClass.ofState ⟨C.depth,C.fill H.graph,(.search,.input 0)⟩)
  rw [← StateClass.initial_iso li,← StateClass.initial_iso ri]
  cases pair with
  | expand context F K edges =>
    let S : Specimen T bindingFreeContexts :=
      ⟨C.depth,C.graph,C.bindingFree,C.bindingFree.1,F,K,edges,lc,rc,(.search,.input 0),rfl⟩
    exact initial_lifting T bindingFreeContexts closed S

/-- The concrete forward robustness theorem, quantified over all original
closing contexts at unrestricted surrounding depth. -/
theorem contextual_refines {Q P R : CostOrder} (reasonable : Reasonable Q P R)
    (safe : (system T bindingFreeContexts closed).InputSafe Q P)
    (robust : (system T bindingFreeContexts closed).Robust Q P R)
    {d k h} (G H : OpenProgram d k h) (rel : T.Rel G.graph H.graph) :
    Combined.execution.Refines Q G H := fun C =>
  sufficiency T bindingFreeContexts closed reasonable safe robust (closing_initial_lifting T closed C G H rel)

/-- Converse robustness retains its converse-cost safety requirement. -/
theorem contextual_refines_converse {Q P R : CostOrder} (reasonable : Reasonable Q P R)
    (safe : (system T bindingFreeContexts closed).InputSafe Q.converse P)
    (robust : (system T bindingFreeContexts closed).opposite.Robust Q P R)
    {d k h} (G H : OpenProgram d k h) (rel : T.Rel G.graph H.graph) :
    Combined.execution.Refines Q H G := fun C =>
  sufficiency_converse T bindingFreeContexts closed reasonable safe robust
    (closing_initial_lifting T closed C G H rel)

/-- Both proved template directions yield quantitative contextual equivalence
of the actual open program graphs, with arbitrary variable and atom interfaces. -/
theorem contextual_equiv {Q P R : CostOrder} (reasonable : Reasonable Q P R)
    (safe : (system T bindingFreeContexts closed).InputSafe Q P)
    (safeConverse : (system T bindingFreeContexts closed).InputSafe Q.converse P)
    (robust : (system T bindingFreeContexts closed).Robust Q P R)
    (robustConverse : (system T bindingFreeContexts closed).opposite.Robust Q P R)
    {d k h} (G H : OpenProgram d k h) (rel : T.Rel G.graph H.graph) :
    Combined.execution.Equiv Q G H :=
  ⟨contextual_refines T closed reasonable safe robust G H rel,
    contextual_refines_converse T closed reasonable safeConverse robustConverse G H rel⟩

/-- Forgetting costs only here yields termination equivalence in every original
binding-free context. This includes divergent and stuck observations. -/
theorem contextual_termination
    (safe : (system T bindingFreeContexts closed).InputSafe CostOrder.any CostOrder.improvement)
    (robust : (system T bindingFreeContexts closed).Robust CostOrder.any CostOrder.improvement CostOrder.any)
    (robustConverse : (system T bindingFreeContexts closed).opposite.Robust CostOrder.any CostOrder.improvement CostOrder.any)
    {d k h} (G H : OpenProgram d k h) (rel : T.Rel G.graph H.graph) (C : ClosingContext d k h) :
    Combined.execution.Terminates (C.close G) ↔ Combined.execution.Terminates (C.close H) :=
  (Combined.execution.equiv_any_iff G H).mp
    (contextual_equiv T closed CostOrder.reasonable_termination safe safe robust robustConverse G H rel) C

/-- Application to the unchanged Figure 16 translations at every adequate
allowance. Template membership and its safety/robustness remain application proofs. -/
theorem term_equiv
    (safe : (system T bindingFreeContexts closed).InputSafe CostOrder.any CostOrder.improvement)
    (robust : (system T bindingFreeContexts closed).Robust CostOrder.any CostOrder.improvement CostOrder.any)
    (robustConverse : (system T bindingFreeContexts closed).opposite.Robust CostOrder.any CostOrder.improvement CostOrder.any)
    {k h} (t u : Term k h)
    (related : ∀ d (ht : Translation.depth t ≤ d) (hu : Translation.depth u ≤ d),
      T.Rel (translatedProgram t d ht).graph (translatedProgram u d hu).graph) :
    ObservationalEquiv Combined.execution t u := fun d ht hu =>
  contextual_equiv T closed CostOrder.reasonable_termination safe safe robust robustConverse
    (translatedProgram t d ht) (translatedProgram u d hu) (related d ht hu)
end Specimens
end Hypernets.Copying
