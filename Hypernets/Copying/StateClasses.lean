import Hypernets.Copying.DeepFillings

/-! The full copying machine on recursive-renaming and depth-padding classes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- Structural representation changes, never computation steps. -/
inductive Representation : UnboundedState → UnboundedState → Prop where
  | iso {s t} : Represents s t → Representation s t
  | padding (s) : Representation s (padUnbounded s)
  | refl (s) : Representation s s
  | symm {s t} : Representation s t → Representation t s
  | trans {s t u} : Representation s t → Representation t u → Representation s u

namespace Representation

theorem final_iff {s t} (h : Representation s t) : unboundedMachine.final s ↔ unboundedMachine.final t := by
  induction h with
  | iso h => exact represents_final h
  | padding s => exact (padUnbounded_final s).symm
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik

theorem rooted_iff {s t} (h : Representation s t) : UnboundedRooted s ↔ UnboundedRooted t := by
  induction h with
  | iso h => exact represents_rooted h
  | padding s =>
    rcases s with ⟨d,G,p⟩
    exact ((Padding.search G).rooted_iff p).symm
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik

/-- Every representation generator is an exact one-step bisimulation. The
reverse padding case uses the proved match-reflection theorem, not determinism. -/
theorem bisimulation {s t} (h : Representation s t) :
    (∀ s', UnboundedStep s s' → ∃ t', UnboundedStep t t' ∧ Representation s' t') ∧
    (∀ t', UnboundedStep t t' → ∃ s', UnboundedStep s s' ∧ Representation s' t') := by
  induction h with
  | iso h =>
    constructor
    · intro s' step
      obtain ⟨t',step',rel⟩ := unbounded_step_transport step h
      exact ⟨t',step',.iso rel⟩
    · intro t' step
      obtain ⟨s',step',rel⟩ := unbounded_step_transport step (represents_symm h)
      exact ⟨s',step',.iso (represents_symm rel)⟩
  | padding s =>
    constructor
    · intro s' step; exact ⟨padUnbounded s',unbounded_step_padding step,.padding s'⟩
    · intro t' step
      obtain ⟨s',run,rel⟩ := unbounded_run_reflect_padding (Machine.Steps.cons step (.zero _))
      cases run with
      | cons first rest =>
        have eq := rest.zero_eq
        subst s'
        exact ⟨_,first,(Representation.padding _).trans (.iso rel)⟩
  | refl s => exact ⟨fun t h => ⟨t,h,.refl t⟩,fun t h => ⟨t,h,.refl t⟩⟩
  | symm h ih =>
    exact ⟨fun _ step => by obtain ⟨t,s,h⟩ := ih.2 _ step; exact ⟨t,s,h.symm⟩,
      fun _ step => by obtain ⟨t,s,h⟩ := ih.1 _ step; exact ⟨t,s,h.symm⟩⟩
  | trans h k ih ik =>
    constructor
    · intro s' step
      obtain ⟨t',a,rel⟩ := ih.1 _ step
      obtain ⟨u',b,rel'⟩ := ik.1 _ a
      exact ⟨u',b,rel.trans rel'⟩
    · intro u' step
      obtain ⟨t',a,rel⟩ := ik.2 _ step
      obtain ⟨s',b,rel'⟩ := ih.2 _ a
      exact ⟨s',b,rel'.trans rel⟩

theorem transport {s t s'} (h : Representation s t) (step : UnboundedStep s s') :
    ∃ t', UnboundedStep t t' ∧ Representation s' t' := h.bisimulation.1 _ step
end Representation

def representationSetoid : Setoid UnboundedState where
  r := Representation
  iseqv := ⟨Representation.refl,Representation.symm,Representation.trans⟩

abbrev StateClass := Quotient representationSetoid
namespace StateClass

def ofState (s : UnboundedState) : StateClass := Quotient.mk representationSetoid s

def Final : StateClass → Prop := Quotient.lift (fun s => unboundedMachine.final s)
  (fun _ _ h => propext h.final_iff)
def Rooted : StateClass → Prop := Quotient.lift UnboundedRooted (fun _ _ h => propext h.rooted_iff)

/-- Exactly one old machine step on some representatives. Padding has zero
cost as a representation equality and is never added as a machine transition. -/
def Step (s t : StateClass) : Prop := ∃ a b, s = ofState a ∧ t = ofState b ∧ UnboundedStep a b

theorem project {s t} (step : UnboundedStep s t) : Step (ofState s) (ofState t) := ⟨s,t,rfl,rfl,step⟩

/-- Any class step lifts from any specified source representative. -/
theorem reflect {s t} (step : Step (ofState s) t) : ∃ u, UnboundedStep s u ∧ t = ofState u := by
  obtain ⟨a,b,eq,target,step⟩ := step
  have rel : Representation s a := Quotient.exact eq
  obtain ⟨u,step',hu⟩ := rel.bisimulation.2 _ step
  exact ⟨u,step',target.trans (Quotient.sound hu).symm⟩

theorem deterministic {s t u} (a : Step s t) (b : Step s u) : t = u := by
  obtain ⟨x,y,eq,ty,a⟩ := a
  rw [eq] at b
  obtain ⟨z,b,uz⟩ := reflect b
  exact ty.trans ((Quotient.sound (Representation.iso (unbounded_deterministic a b))).trans uz.symm)

theorem final_normal {s} (final : Final s) : ∀ t, ¬ Step s t := by
  rintro t ⟨a,b,eq,_,step⟩
  rw [eq] at final
  exact unbounded_final_normal final b step

def machine : Machine StateClass where
  step := Step
  final := Final
  final_normal h := final_normal h _

theorem machine_deterministic : machine.Deterministic := fun _ _ _ => deterministic

theorem rooted_step {s t} (root : Rooted s) (step : Step s t) : Rooted t := by
  obtain ⟨a,b,eq,target,step⟩ := step
  rw [eq] at root; rw [target]
  exact unbounded_refocusing root step

theorem project_run {s t n} (run : unboundedMachine.Steps n s t) :
    machine.Steps n (ofState s) (ofState t) := by
  induction run with
  | zero => exact .zero _
  | cons first rest ih => exact .cons (project first) ih

/-- An entire class run has an exact representative run, from the chosen start
and hence at its original finite allowance. -/
theorem reflect_run {s t n} (run : machine.Steps n s t) :
    ∀ a, s = ofState a → ∃ b, unboundedMachine.Steps n a b ∧ t = ofState b := by
  induction run with
  | zero => intro a eq; exact ⟨a,.zero _,eq⟩
  | cons step rest ih =>
    intro a eq
    rw [eq] at step
    obtain ⟨b,first,beq⟩ := reflect step
    obtain ⟨c,tail,ceq⟩ := ih b beq
    exact ⟨c,.cons first tail,ceq⟩

theorem successful_iff (s : UnboundedState) (n : Nat) :
    (∃ t, machine.Steps n (ofState s) t ∧ machine.final t) ↔
      ∃ t, unboundedMachine.Steps n s t ∧ unboundedMachine.final t := by
  constructor
  · rintro ⟨t,run,final⟩
    obtain ⟨u,run,eq⟩ := reflect_run run s rfl
    exact ⟨u,run,by rw [eq] at final; exact final⟩
  · rintro ⟨t,run,final⟩; exact ⟨ofState t,project_run run,final⟩

/-- Quantitative refinement on classes is exactly the existing concrete observation. -/
theorem refines_iff (Q : CostOrder) (s t : UnboundedState) :
    machine.Refines Q (ofState s) (ofState t) ↔ unboundedMachine.Refines Q s t := by
  constructor
  · intro h n u run final
    obtain ⟨m,v,cost,tail,done⟩ := h (project_run run) final
    obtain ⟨w,tail,eq⟩ := reflect_run tail t rfl
    exact ⟨m,w,cost,tail,by rw [eq] at done; exact done⟩
  · intro h n u run final
    obtain ⟨v,run,eq⟩ := reflect_run run s rfl
    obtain ⟨m,w,cost,tail,done⟩ := h run (by rw [eq] at final; exact final)
    exact ⟨m,ofState w,cost,project_run tail,done⟩

/-- Initialisation uses the unchanged program graph. -/
def execution : Execution StateClass where
  machine := machine
  initial P := ofState (Combined.execution.initial P)
end StateClass
end Hypernets.Copying.Combined
