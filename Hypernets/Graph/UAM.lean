import Hypernets.Graph.Substitution

/-! Concrete linear Universal Abstract Machine, paper §6.4. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace State
/-- The shape restriction on extrinsic transitions: rewrite focus entering an
active operation, with a search focus in the result. No locality is required. -/
def Compute (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  s.focussed.mode = .rewrite ∧ t.focussed.mode = .search ∧
    ∃ (e : s.graph.Edge) (o : Op),
      s.graph.edgeLabel e = primitiveLabel ops d (.operation o) ∧
      kind o = .active ∧ s.graph.source e = [s.focussed.target]

/-- A computation and a substitution cannot start in the same state. -/
theorem substitution_not_compute {kind : Op → OperationKind} {s t u : State ops d}
    (sub : Substitution s t) (compute : Compute kind s u) : False := by
  obtain ⟨v,vl,vs⟩ := substitution_variable sub
  obtain ⟨_,_,e,o,el,_,es⟩ := compute
  have eq : v = e := s.graph.source_unique (v := s.focussed.target) (by rw [vs]; simp) (by rw [es]; simp)
  have bad := primitiveLabel_injective d (vl.symm.trans ((congrArg s.graph.edgeLabel eq).trans el))
  cases bad

/-- A search step cannot start at a rewrite focus. -/
theorem search_not_rewrite {kind : Op → OperationKind} {s t : State ops d}
    (step : Search kind s t) : s.focussed.mode ≠ .rewrite := by
  intro mode
  obtain ⟨q,step,_⟩ := step
  have eq : (coordinate s).val = (.rewrite,(coordinate s).val.2) := by
    apply Prod.ext
    · exact mode
    · rfl
  rw [eq] at step
  exact SearchStep.no_rewrite step
end State

/-- The behaviour parameter contains only compute transitions (§6.4).
Determinism is deliberately not assumed by the machine definition. -/
structure Behaviour (ops : Operations Op) (d : Nat) (kind : Op → OperationKind) where
  step : State ops d → State ops d → Prop
  compute : ∀ {s t}, step s t → State.Compute kind s t

namespace UAM
variable {kind : Op → OperationKind} (B : Behaviour ops d kind)

/-- The two intrinsic transition families, independent of the behaviour. -/
def Intrinsic (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  State.Search kind s t ∨ State.Substitution s t

/-- The full UAM: search, substitution, or the supplied extrinsic behaviour. -/
def Step (s t : State ops d) : Prop :=
  Intrinsic kind s t ∨ B.step s t

/-- Rewrite transitions are substitution and compute behaviour together. -/
def Rewrite (s t : State ops d) : Prop := State.Substitution s t ∨ B.step s t

/-- Every rewrite consumes a rewrite focus and restarts search. -/
theorem rewrite_modes {s t : State ops d} (step : Rewrite B s t) :
    s.focussed.mode = .rewrite ∧ t.focussed.mode = .search := by
  rcases step with sub | ext
  · exact State.substitution_modes sub
  · exact ⟨(B.compute ext).1,(B.compute ext).2.1⟩

/-- Every machine step is either search or rewrite. -/
theorem step_iff {s t : State ops d} : Step B s t ↔ State.Search kind s t ∨ Rewrite B s t := by
  exact or_assoc

/-- Search and rewrite are exclusive, even when their proposed targets differ. -/
theorem search_rewrite_exclusive {s t u : State ops d}
    (search : State.Search kind s t) (rewrite : Rewrite B s u) : False :=
  State.search_not_rewrite search (rewrite_modes B rewrite).1

/-- The intrinsic and extrinsic parts are disjoint at their sources. -/
theorem intrinsic_extrinsic_exclusive {s t u : State ops d}
    (intrinsic : Intrinsic kind s t) (ext : B.step s u) : False := by
  rcases intrinsic with search | sub
  · exact State.search_not_rewrite search (B.compute ext).1
  · exact State.substitution_not_compute sub (B.compute ext)

/-- Final states have no successor under any admissible behaviour. -/
theorem final_normal {s t : State ops d} (final : s.focussed.Final) : ¬ Step B s t := by
  intro step
  rcases (step_iff B).mp step with search | rewrite
  · exact State.final_no_search final search
  · have bad := final.1.symm.trans (rewrite_modes B rewrite).1
    cases bad

/-- A concrete instance of the transition-system interface used by counting
simulations. Determinism/refocusing and the specimen interface remain separate. -/
def machine : Machine (State ops d) where
  step := Step B
  final s := s.focussed.Final
  final_normal := final_normal B

/-- The empty behaviour is admissible for every operation partition. -/
def emptyBehaviour (ops : Operations Op) (d : Nat) (kind : Op → OperationKind) :
    Behaviour ops d kind := ⟨fun _ _ => False,fun h => False.elim h⟩

/-- With no extrinsic rules, exactly the intrinsic transitions remain. -/
theorem empty_step {s t : State ops d} :
    Step (emptyBehaviour ops d kind) s t ↔ Intrinsic kind s t := by
  simp [Step,emptyBehaviour]
end UAM
end Hypernets.Linear
