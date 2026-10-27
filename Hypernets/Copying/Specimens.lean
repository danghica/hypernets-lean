import Hypernets.Copying.StateClasses

/-! Concrete copying specimens and synchronized traversal of their shared context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion Combined

/-- At non-rewrite mode the full machine contains only genuine search. -/
theorem Combined.nonrewrite_search {d I O} {s t : Combined.State d I O}
    (mode : s.2.1 ≠ .rewrite) (step : Combined.Step s t) :
    ∃ q, Search.Step s.1 s.2 q ∧ t = ⟨s.1,q⟩ := by
  cases step with
  | search G h => exact ⟨_,h,rfl⟩
  | rewrite h => exact False.elim (mode rfl)

/-- Related recursive fillings of a focus-free context, with a typed outer token.
The context class is explicit; the final application will use binding-free contexts.
Global hole freedom is checked on the actual filled graphs. -/
structure Specimen (T : PreTemplate) (Allowed : ∀ d, Hypernet d [.term] [] → Prop) where
  depth : Nat
  context : Hypernet depth [.term] []
  allowed : Allowed depth context
  free : FocusFree context
  left : (e : context.Edge) → Hypernet depth ((alphabet depth).signature.input (context.edgeLabel e))
    ((alphabet depth).signature.output (context.edgeLabel e))
  right : (e : context.Edge) → Hypernet depth ((alphabet depth).signature.input (context.edgeLabel e))
    ((alphabet depth).signature.output (context.edgeLabel e))
  edges : ∀ e, DeepFillingEdge T context left right e
  left_closed : HoleFree (context.expand left)
  right_closed : HoleFree (context.expand right)
  token : Search.Position context
  term : context.vertexLabel token.2 = .term

namespace Specimen
variable {T Allowed} (S : Specimen T Allowed)

def leftState : UnboundedState := ⟨S.depth,S.context.expand S.left,position S.context S.left S.token⟩
def rightState : UnboundedState := ⟨S.depth,S.context.expand S.right,position S.context S.right S.token⟩
def Entering : Prop := Search.Expansion.Entering S.context S.token

theorem filled_free : FocusFree S.leftState.2.1 ∧ FocusFree S.rightState.2.1 :=
  (DeepFilling.expand S.context S.left S.right S.edges).focusFree S.free

/-- Moving the token changes neither graph, any hole filling, nor its allowed context. -/
def relocate (p : Search.Position S.context) (typed : S.context.vertexLabel p.2 = .term) : Specimen T Allowed :=
  { S with token := p, term := typed }

theorem same_final : unboundedMachine.final S.leftState ↔ unboundedMachine.final S.rightState := by
  change (S.token.1 = .backtrack ∧ (Net.Expansion.host S.context S.left S.token.2).IsInput) ↔
    (S.token.1 = .backtrack ∧ (Net.Expansion.host S.context S.right S.token.2).IsInput)
  cases S.token.2 <;> rfl

/-- A step on either settled rooted side yields synchronized steps of the actual
full machine and a remote successor specimen with exactly the same fillings. -/
theorem context_step (closed : T.OutputClosed)
    (leftRoot : UnboundedRooted S.leftState) (rightRoot : UnboundedRooted S.rightState)
    (settled : S.token.1 = .backtrack ∨ (S.token.1 = .search ∧ ¬ S.Entering))
    (enabled : (∃ t, UnboundedStep S.leftState t) ∨ (∃ t, UnboundedStep S.rightState t)) :
    ∃ D : Specimen T Allowed, (D.token.1 ≠ .rewrite ∨ ¬ D.Entering) ∧
      UnboundedStep S.leftState D.leftState ∧ UnboundedStep S.rightState D.rightState := by
  have laws := deepFilling_search S.edges
  have away := settled_away S.context S.left (deepFilling_outputClosed S.edges closed)
    S.token S.term leftRoot rightRoot settled
  have nonrewrite : S.token.1 ≠ .rewrite := by rcases settled with h | ⟨h,_⟩ <;> rw [h] <;> decide
  have get {F} (origins : Origins S.context F) (preserves : Preserves S.context F)
      {t} (step : UnboundedStep ⟨S.depth,S.context.expand F,position S.context F S.token⟩ t) :
      ∃ q, Search.Step S.context S.token q := by
    cases step with
    | lift finite =>
      obtain ⟨q,h,_⟩ := Combined.nonrewrite_search nonrewrite finite
      obtain ⟨r,original,_⟩ := (step_iff S.context F preserves origins S.token away).mp h
      exact ⟨r,original⟩
  have someStep : ∃ q, Search.Step S.context S.token q := by
    rcases enabled with ⟨t,h⟩ | ⟨t,h⟩
    · exact get laws.2.2.1 laws.1 h
    · exact get laws.2.2.2 laws.2.1 h
  obtain ⟨q,step⟩ := someStep
  refine ⟨S.relocate q (Search.endpoints_term step).2,remote_target S.context step,?_,?_⟩
  · exact .lift (.search _ (Search.Expansion.step S.context S.left laws.1 step))
  · exact .lift (.search _ (Search.Expansion.step S.context S.right laws.2.1 step))

/-- The context's initial coordinate gives rooted initial states on both sides. -/
def initial : Specimen T Allowed := S.relocate (.search,.input 0) rfl

theorem initial_rooted : UnboundedRooted S.initial.leftState ∧ UnboundedRooted S.initial.rightState :=
  ⟨Search.rooted_initial (S.context.expand S.left) 0,Search.rooted_initial (S.context.expand S.right) 0⟩
end Specimen

namespace Combined.StateClass
/-- Reflection from a non-rewrite source extracts actual search at that exact allowance. -/
theorem search_of_nonrewrite {d} {s : Combined.State d [.term] []} {t}
    (mode : s.2.1 ≠ .rewrite) (step : Step (ofState ⟨d,s⟩) t) :
    ∃ q, Search.Step s.1 s.2 q ∧ t = ofState ⟨d,s.1,q⟩ := by
  obtain ⟨u,ustep,eq⟩ := reflect step
  cases ustep with
  | lift finite =>
    obtain ⟨q,h,target⟩ := Combined.nonrewrite_search mode finite
    subst target
    exact ⟨q,h,eq⟩
end Combined.StateClass

namespace Specimens
variable (T : PreTemplate) (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (closed : T.OutputClosed)

/-- Every abstract machine-law and context-locality field is proved. The only
semantic parameter is output closure of the proposed template, as in the paper. -/
def system : SpecimenSystem StateClass.machine where
  Specimen := Copying.Specimen T Allowed
  left S := StateClass.ofState S.leftState
  right S := StateClass.ofState S.rightState
  mode S := S.token.1
  entering S := S.Entering
  rooted := StateClass.Rooted
  rooted_step := StateClass.rooted_step
  same_final := Specimen.same_final
  context_step := by
    intro S left right settled enabled
    have available : (∃ t, UnboundedStep S.leftState t) ∨ (∃ t, UnboundedStep S.rightState t) := by
      rcases enabled with ⟨t,step⟩ | ⟨t,step⟩
      · obtain ⟨u,h,_⟩ := StateClass.reflect step; exact .inl ⟨u,h⟩
      · obtain ⟨u,h,_⟩ := StateClass.reflect step; exact .inr ⟨u,h⟩
    obtain ⟨D,remote,l,r⟩ := S.context_step closed left right settled available
    exact ⟨D,remote,StateClass.project l,StateClass.project r⟩

/-- Initial paired fillings supply the actual lifting witnesses. -/
theorem initial_lifting (S : Copying.Specimen T Allowed) :
    (system T Allowed closed).Lifting (StateClass.ofState S.initial.leftState)
      (StateClass.ofState S.initial.rightState) :=
  ⟨S.initial,.inl (by change Focus.search ≠ Focus.rewrite; decide),S.initial_rooted.1,S.initial_rooted.2,rfl,rfl⟩

/-- Forward robustness reasoning now applies to this concrete copying machine.
Only the proposed template's safety/robustness and cost conditions remain. -/
theorem sufficiency {Q P R : CostOrder} (reasonable : Reasonable Q P R)
    (safe : (system T Allowed closed).InputSafe Q P)
    (robust : (system T Allowed closed).Robust Q P R) {s t : UnboundedState}
    (related : (system T Allowed closed).Lifting (StateClass.ofState s) (StateClass.ofState t)) :
    unboundedMachine.Refines Q s t :=
  (StateClass.refines_iff Q s t).mp ((system T Allowed closed).sufficiency
    StateClass.machine_deterministic reasonable safe robust related)

/-- The converse clause retains the original converse-cost safety requirement. -/
theorem sufficiency_converse {Q P R : CostOrder} (reasonable : Reasonable Q P R)
    (safe : (system T Allowed closed).InputSafe Q.converse P)
    (robust : (system T Allowed closed).opposite.Robust Q P R) {s t : UnboundedState}
    (related : (system T Allowed closed).Lifting (StateClass.ofState s) (StateClass.ofState t)) :
    unboundedMachine.Refines Q t s :=
  (StateClass.refines_iff Q t s).mp ((system T Allowed closed).sufficiency_converse
    StateClass.machine_deterministic reasonable safe robust related)
end Specimens
end Hypernets.Copying
