import Hypernets.Copying.CombinedExecution
import Hypernets.Copying.SearchTyping

/-! Every interaction in the contextual subsystem is on a term wire.
Typed insertion preserves this fact even when a local boundary becomes internal. -/
namespace Hypernets.Copying.Combined
open Graph

/-- Both active coordinates of each local compute or copy rule are term typed. -/
theorem local_endpoints_term {d I O} {G H : Hypernet d I O} {v w}
    (step : Local G v H w) : G.vertexLabel v = .term ∧ H.vertexLabel w = .term := by
  cases step <;> constructor <;> rfl

/-- Renaming and both forms of shallow context closure preserve active-wire typing. -/
theorem rewrite_endpoints_term {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) : G.vertexLabel v = .term ∧ H.vertexLabel w = .term := by
  induction step with
  | «local» step => exact local_endpoints_term step
  | rename f g step ih =>
    exact ⟨((BoundaryIso.ofDeepIso f).vertex_label _).trans ih.1,
      ((BoundaryIso.ofDeepIso g).vertex_label _).trans ih.2⟩
  | plug C e step ih =>
    exact ⟨(Net.Replacement.insert_label C e _ _).trans ih.1,
      (Net.Replacement.insert_label C e _ _).trans ih.2⟩
  | expand C F K e others step ih =>
    exact ⟨(Net.Expansion.insert_label C F e _).trans ih.1,
      (Net.Expansion.insert_label C K e _).trans ih.2⟩

theorem step_endpoints_term {d I O} {s t : State d I O} (step : Step s t) :
    s.1.vertexLabel s.2.2 = .term ∧ t.1.vertexLabel t.2.2 = .term := by
  cases step with
  | search G step => exact Search.endpoints_term step
  | rewrite step => exact rewrite_endpoints_term step

/-- A typed starting token remains term typed throughout any finite execution. -/
theorem run_term {d I O} {s t : State d I O} {n}
    (run : (machine d I O).Steps n s t) (typed : s.1.vertexLabel s.2.2 = .term) :
    t.1.vertexLabel t.2.2 = .term := by
  induction run with
  | zero => exact typed
  | cons step rest ih => exact ih (step_endpoints_term step).2

theorem unbounded_step_term {s t : UnboundedState} (step : UnboundedStep s t) :
    s.2.1.vertexLabel s.2.2.2 = .term ∧ t.2.1.vertexLabel t.2.2.2 = .term := by
  cases step with | lift step => exact step_endpoints_term step

/-- Every state reached from an actual closed program has a term-typed token. -/
theorem reachable_term (P : ClosedProgram) {n t}
    (run : unboundedMachine.Steps n (execution.initial P) t) :
    t.2.1.vertexLabel t.2.2.2 = .term := by
  obtain ⟨b,eq,bounded⟩ := run_bounded run (execution.initial P).2 rfl
  subst t
  exact run_term bounded rfl
end Hypernets.Copying.Combined
