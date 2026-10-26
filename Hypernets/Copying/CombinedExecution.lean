import Hypernets.Copying.CombinedLocality

/-! An unbounded allowance-indexed execution instance for the proved-rule subsystem.
The complete paper UAM still requires matching independence and refocusing. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

abbrev UnboundedState := Σ d, State d [.term] []
inductive UnboundedStep : UnboundedState → UnboundedState → Prop where
  | lift {d} {s t : State d [.term] []} : Step s t → UnboundedStep ⟨d,s⟩ ⟨d,t⟩

theorem unbounded_final_normal {s : UnboundedState} (done : Search.Completed s.2.2) :
    ∀ t, ¬ UnboundedStep s t := by
  intro t step; cases step with
  | lift step => exact final_normal done _ step

def unboundedMachine : Machine UnboundedState where
  step := UnboundedStep
  final s := Search.Completed s.2.2
  final_normal h := unbounded_final_normal h _

/-- Initialization preserves the supplied closed graph and starts search at its input. -/
def execution : Execution UnboundedState where
  machine := unboundedMachine
  initial P := ⟨P.depth,P.graph,(.search,.input 0)⟩

/-- A transition never changes its representation allowance. -/
theorem step_depth {s t : UnboundedState} (step : UnboundedStep s t) : s.1 = t.1 := by
  cases step; rfl

theorem run_depth {s t : UnboundedState} {n} (run : unboundedMachine.Steps n s t) : s.1 = t.1 := by
  induction run with
  | zero => rfl
  | cons step run ih => exact (step_depth step).trans ih

/-- Every fixed-allowance execution is an actual execution of the unbounded subsystem. -/
theorem run_unbounded {d} {s t : State d [.term] []} {n} (run : (machine d [.term] []).Steps n s t) :
    unboundedMachine.Steps n ⟨d,s⟩ ⟨d,t⟩ := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (.lift step) ih

/-- No hidden transitions are introduced by the unbounded state wrapper. -/
theorem run_bounded {s t : UnboundedState} {n} (run : unboundedMachine.Steps n s t) :
    ∀ {d} (a : State d [.term] []), s = ⟨d,a⟩ →
      ∃ b, t = ⟨d,b⟩ ∧ (machine d [.term] []).Steps n a b := by
  induction run with
  | zero =>
    intro d a eq; subst eq
    exact ⟨a,rfl,.zero _⟩
  | @cons n s u t first rest ih =>
    cases first with
    | @lift e x y first =>
      intro d a eq
      cases eq
      obtain ⟨b,endEq,rest⟩ := ih y rfl
      exact ⟨b,endEq,.cons first rest⟩

/-- Exact finite-run correspondence at every fixed allowance, in both directions. -/
theorem run_unbounded_iff {d} {s t : State d [.term] []} {n} :
    unboundedMachine.Steps n ⟨d,s⟩ ⟨d,t⟩ ↔ (machine d [.term] []).Steps n s t := by
  constructor
  · intro run
    obtain ⟨b,eq,bounded⟩ := run_bounded run s rfl
    have same : t = b := by cases eq; rfl
    simpa only [same] using bounded
  · exact run_unbounded

/-- Isomorphic unbounded states have the same allowance and related token positions. -/
inductive Represents : UnboundedState → UnboundedState → Prop where
  | lift {d} {s t : State d [.term] []} (iso : StateIso s t) : Represents ⟨d,s⟩ ⟨d,t⟩

theorem represents_symm {s t : UnboundedState} (f : Represents s t) : Represents t s := by
  cases f with | lift f => exact .lift f.symm

theorem represents_final {s t : UnboundedState} (f : Represents s t) :
    unboundedMachine.final s ↔ unboundedMachine.final t := by
  cases f with | lift f => exact f.final_iff

theorem unbounded_step_transport {s t s' : UnboundedState} (step : UnboundedStep s t)
    (f : Represents s s') : ∃ t', UnboundedStep s' t' ∧ Represents t t' := by
  cases f with
  | lift f =>
    cases step with
    | lift step =>
      obtain ⟨v,step',⟨g⟩⟩ := step_transport step f
      exact ⟨⟨_,v⟩,.lift step',.lift g⟩

theorem unbounded_run_transport {s t s' : UnboundedState} {n}
    (run : unboundedMachine.Steps n s t) (f : Represents s s') :
    ∃ t', unboundedMachine.Steps n s' t' ∧ Represents t t' := by
  induction run generalizing s' with
  | zero => exact ⟨s',.zero _,f⟩
  | cons step run ih =>
    obtain ⟨v,first,g⟩ := unbounded_step_transport step f
    obtain ⟨t',rest,h⟩ := ih g
    exact ⟨t',.cons first rest,h⟩

/-- Representation changes preserve every successful cost, hence every cost preorder. -/
theorem represents_refines (Q : CostOrder) {s t : UnboundedState} (f : Represents s t) :
    unboundedMachine.Refines Q s t := by
  intro n u run done
  obtain ⟨v,run',g⟩ := unbounded_run_transport run f
  exact ⟨n,v,Q.refl n,run',represents_final g |>.mp done⟩

theorem represents_equiv (Q : CostOrder) {s t : UnboundedState} (f : Represents s t) :
    unboundedMachine.Equiv Q s t := ⟨represents_refines Q f,represents_refines Q (represents_symm f)⟩

/-- This previously abstract interface law is discharged for the concrete subsystem. -/
theorem execution_respectsIso : execution.RespectsIso := by
  intro d G H gf gh hf hh f
  exact represents_equiv CostOrder.any (.lift {graph := f, mode := rfl, vertex := rfl})

/-- Contextual congruence now has no execution-isomorphism premise for this subsystem. -/
theorem equiv_context {r v a d k h} (D : GraphContext r v a d k h) {G H : OpenProgram r v a}
    (rel : execution.Equiv CostOrder.any G H) :
    execution.Equiv CostOrder.any (D.fill G) (D.fill H) :=
  execution.equiv_context execution_respectsIso D rel
end Hypernets.Copying.Combined
