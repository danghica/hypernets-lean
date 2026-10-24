import Hypernets.Graph.UnboundedUAM

/-! Determinism on the unbounded carrier follows from the extrinsic relation alone. -/
namespace Hypernets.Linear.Unbounded
open Graph
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- Compute admissibility is unchanged by recursive focus-preserving renaming. -/
theorem compute_iso {n} {s t u v : Linear.State ops n}
    (a : Focussed.DeepIso s.focussed u.focussed) (b : Focussed.DeepIso t.focussed v.focussed)
    (h : Linear.State.Compute kind s t) : Linear.State.Compute kind u v := by
  obtain ⟨sm,tm,e,o,lab,active,src⟩ := h
  refine ⟨a.mode.symm.trans sm,b.mode.symm.trans tm,a.graph.edges.toFun e,o,
    labelEquiv_primitive (a.graph.edge_label e) (.operation o) lab,active,?_⟩
  rw [← a.graph.source,src,List.map_cons,List.map_nil,a.target]

/-- Restricting a behaviour on the quotient automatically respects all recursive names. -/
theorem Behaviour.respectsIso (B : Behaviour ops kind) (n : Nat) : (B.atDepth n).RespectsIso := by
  intro s t u v a b h
  refine ⟨?_,compute_iso a b h.2⟩
  have ha : DeepStateClass.ofState s = DeepStateClass.ofState u := Quotient.sound ⟨a⟩
  have hb : DeepStateClass.ofState t = DeepStateClass.ofState v := Quotient.sound ⟨b⟩
  change B.step (ofClass (DeepStateClass.ofState u)) (ofClass (DeepStateClass.ofState v))
  rw [← ha,← hb]
  exact h.1

/-- Determinism is a property of the extrinsic relation on actual unbounded states. -/
def Behaviour.Deterministic (B : Behaviour ops kind) : Prop :=
  ∀ {s t u}, B.step s t → B.step s u → t = u

/-- Faithful finite-depth embeddings reflect extrinsic determinism. -/
theorem Behaviour.deterministicAt (B : Behaviour ops kind) (det : B.Deterministic) (n : Nat) :
    DeterministicModulo (B.atDepth n).step := by
  intro s t u h g
  have eq := det h.1 g.1
  exact Quotient.exact (ofClass_injective eq)

/-- Two staged edges with a shared source agree when each layer is deterministic. -/
theorem at_deterministic {R : Relations ops}
    (det : ∀ n {s t u}, R n s t → R n s u → t = u)
    {s t u} (h : At R s t) (g : At R s u) : t = u := by
  cases h with
  | edge h =>
    cases g with
    | edge g => exact congrArg (Sigma.mk _) (det _ h g)

/-- Determinism passes to the union after aligning both source presentations. -/
theorem step_deterministic {R : Relations ops} (pres : Preserved R)
    (det : ∀ n {s t u}, R n s t → R n s u → t = u)
    {s t u} (h : Step R s t) (g : Step R s u) : t = u := by
  obtain ⟨a,b,ha,hb,h⟩ := h
  obtain ⟨c,e,hc,he,g⟩ := g
  obtain ⟨i,j,eq⟩ := Quotient.exact (ha.trans hc.symm)
  have h := at_advance pres i h
  have g := at_advance pres j g
  rw [eq] at h
  have ends := congrArg ofStage (at_deterministic det h g)
  rw [ofStage_advance,ofStage_advance,hb,he] at ends
  exact ends

/-- The unbounded full UAM is deterministic whenever its extrinsic behaviour is. -/
theorem deterministic (B : Behaviour ops kind) (det : B.Deterministic) : (machine B).Deterministic := by
  intro s t u h g
  exact step_deterministic (full_preserved B)
    (fun n {_ _ _} h g => UAMClasses.deterministic (B.atDepth n)
      (B.respectsIso n) (B.deterministicAt det n) h g)
    ((full_step_iff B s t).mpr h) ((full_step_iff B s u).mpr g)

/-- The auxiliary exact-run presentation agrees with the project's machine runs. -/
theorem run_steps_iff {S : Type u} (M : Machine S) {k s t} :
    Run M.step k s t ↔ M.Steps k s t := by
  constructor
  · intro h
    induction h with
    | nil => exact .zero _
    | cons h _ ih => exact .cons h ih
  · intro h
    induction h with
    | zero => exact .nil _
    | cons h _ ih => exact .cons h ih

/-- The full operational transfer in the execution language used by the robustness proof. -/
theorem machine_steps_iff (B : Behaviour ops kind) {k s t} :
    (machine B).Steps k s t ↔ ∃ n, ∃ a b : DeepStateClass ops n,
      ofClass a = s ∧ ofClass b = t ∧ (UAMClasses.machine (B.atDepth n)).Steps k a b := by
  rw [← run_steps_iff]
  constructor
  · intro h
    obtain ⟨n,a,b,ha,hb,run⟩ := (full_run_iff B).mp h
    exact ⟨n,a,b,ha,hb,(run_steps_iff _).mp run⟩
  · rintro ⟨n,a,b,ha,hb,run⟩
    exact (full_run_iff B).mpr ⟨n,a,b,ha,hb,(run_steps_iff _).mpr run⟩
end Hypernets.Linear.Unbounded
