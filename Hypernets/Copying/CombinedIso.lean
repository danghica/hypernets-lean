import Hypernets.Copying.CombinedRules

/-! Recursive representation invariance of complete finite runs of the combined
subsystem. No determinism, refocusing or padding law is assumed here. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- A state isomorphism preserves its focus mode and the actual token vertex. -/
structure StateIso {d I O} (s t : State d I O) where
  graph : DeepIso s.1 t.1
  mode : s.2.1 = t.2.1
  vertex : Port.map graph.vertices.toFun s.2.2 = t.2.2

namespace StateIso
variable {d I O} {s t u : State d I O}
def refl (s : State d I O) : StateIso s s where
  graph := DeepIso.refl _
  mode := rfl
  vertex := by simp [DeepIso.refl,Net.RelIso.refl,Bijection.refl]
def symm (f : StateIso s t) : StateIso t s where
  graph := f.graph.symm
  mode := f.mode.symm
  vertex := by
    rw [← f.vertex]
    exact (Port.bijection f.graph.vertices).left_inv _
def trans (f : StateIso s t) (g : StateIso t u) : StateIso s u where
  graph := f.graph.trans g.graph
  mode := f.mode.trans g.mode
  vertex := by
    change Port.map (g.graph.vertices.toFun ∘ f.graph.vertices.toFun) s.2.2 = _
    have compose : Port.map (g.graph.vertices.toFun ∘ f.graph.vertices.toFun) s.2.2 =
        Port.map g.graph.vertices.toFun (Port.map f.graph.vertices.toFun s.2.2) := by
      cases s.2.2 <;> rfl
    rw [compose,f.vertex,g.vertex]

theorem final_iff (f : StateIso s t) : Search.Completed s.2 ↔ Search.Completed t.2 := by
  have input : s.2.2.IsInput ↔ t.2.2.IsInput := by rw [← f.vertex]; cases s.2.2 <;> rfl
  exact and_congr (by rw [f.mode]) input
end StateIso

/-- One transition transports with exactly one transition and an isomorphic endpoint. -/
theorem step_transport {d I O} {s t s' : State d I O}
    (step : Step s t) (f : StateIso s s') :
    ∃ t', Step s' t' ∧ Nonempty (StateIso t t') := by
  cases step with
  | @search G s t step =>
    let transport := Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.graph)
    refine ⟨⟨s'.1,transport.positions.toFun t⟩,?_,?_⟩
    · have eq : (⟨s'.1,transport.positions.toFun s⟩ : State d I O) = s' := by
        rcases s' with ⟨H,m,v⟩
        apply congrArg (Sigma.mk H)
        exact Prod.ext f.mode f.vertex
      exact Eq.mp (congrArg (fun x => Step x ⟨s'.1,transport.positions.toFun t⟩) eq)
        (.search _ (transport.step step))
    · exact ⟨{ graph := f.graph, mode := rfl, vertex := rfl }⟩
  | @rewrite G H v w step =>
    refine ⟨⟨H,(.search,w)⟩,?_,⟨StateIso.refl _⟩⟩
    have moved := Rewrite.rename f.graph (DeepIso.refl H) step
    have eq : (⟨s'.1,(.rewrite,Port.map f.graph.vertices.toFun v)⟩ : State d I O) = s' := by
      rcases s' with ⟨H,m,v⟩
      apply congrArg (Sigma.mk H)
      exact Prod.ext f.mode f.vertex
    rw [← eq]
    simpa [DeepIso.refl,Net.RelIso.refl,Bijection.refl] using Step.rewrite moved

/-- Transport every step, maintaining the new endpoint isomorphism inductively. -/
theorem run_transport {d I O} {s t : State d I O} {n}
    (run : (machine d I O).Steps n s t) {s'} (f : StateIso s s') :
    ∃ t', (machine d I O).Steps n s' t' ∧ Nonempty (StateIso t t') := by
  induction run generalizing s' with
  | zero => exact ⟨s',.zero _,⟨f⟩⟩
  | cons step run ih =>
    obtain ⟨u',first,⟨g⟩⟩ := step_transport step f
    obtain ⟨t',rest,iso⟩ := ih g
    exact ⟨t',.cons first rest,iso⟩

/-- Exact-cost successful termination, before forgetting costs for observations. -/
def TerminatesIn {d I O} (n : Nat) (s : State d I O) : Prop :=
  ∃ t, (machine d I O).Steps n s t ∧ (machine d I O).final t

theorem terminatesIn_iso {d I O} {s t : State d I O} (f : StateIso s t) (n : Nat) :
    TerminatesIn n s ↔ TerminatesIn n t := by
  constructor
  · rintro ⟨u,run,done⟩
    obtain ⟨v,run',⟨g⟩⟩ := run_transport run f
    exact ⟨v,run',g.final_iff.mp done⟩
  · rintro ⟨u,run,done⟩
    obtain ⟨v,run',⟨g⟩⟩ := run_transport run f.symm
    exact ⟨v,run',g.final_iff.mp done⟩
end Hypernets.Copying.Combined
