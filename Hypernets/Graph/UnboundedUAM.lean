import Hypernets.Graph.DepthSubstitution

/-! The full UAM over the union, allowing extrinsic steps of unbounded finite depth. -/
namespace Hypernets.Linear.Unbounded
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- Compute shape on finite recursive state classes, witnessed by actual states. -/
def ComputeAt (kind : Op → OperationKind) (n : Nat) (s t : DeepStateClass ops n) : Prop :=
  ∃ a b : Linear.State ops n, s = DeepStateClass.ofState a ∧ t = DeepStateClass.ofState b ∧
    Linear.State.Compute kind a b

/-- An extrinsic relation is defined on the union and is restricted only by compute shape.
Its witnesses may use any finite depth; no single global bound is chosen. -/
structure Behaviour (ops : Operations Op) (kind : Op → OperationKind) where
  step : State ops → State ops → Prop
  compute : ∀ {s t}, step s t → Step (ComputeAt kind) s t

/-- Padding a finite class does not change the unbounded state it represents. -/
theorem ofClass_padding {n} (s : DeepStateClass ops n) :
    ofClass (DepthPadding.stateClass s) = ofClass s :=
  ofStage_advance 1 ⟨n,s⟩

/-- Restrict unbounded behaviour to representatives of a given finite depth. -/
def Behaviour.atDepth (B : Behaviour ops kind) (n : Nat) : Linear.Behaviour ops n kind where
  step s t := B.step (ofClass (DeepStateClass.ofState s)) (ofClass (DeepStateClass.ofState t)) ∧
    Linear.State.Compute kind s t
  compute h := h.2

/-- Behaviour preservation is derived from the union definition and concrete shape. -/
theorem Behaviour.padding (B : Behaviour ops kind) {n} (s t : Linear.State ops n)
    (h : (B.atDepth n).step s t) :
    (B.atDepth (n+1)).step (DepthPadding.state s) (DepthPadding.state t) := by
  refine ⟨?_,(DepthPadding.compute_iff kind s t).mpr h.2⟩
  change B.step (ofClass (DepthPadding.stateClass (DeepStateClass.ofState s)))
    (ofClass (DepthPadding.stateClass (DeepStateClass.ofState t)))
  rw [ofClass_padding,ofClass_padding]
  exact h.1

/-- The family of full concrete class machines derived from a global behaviour. -/
def RelationsOf (B : Behaviour ops kind) : Relations ops := fun n => UAMClasses.Step (B.atDepth n)

/-- All three full-UAM transition families satisfy padding compatibility. -/
theorem full_preserved (B : Behaviour ops kind) : Preserved (RelationsOf B) :=
  fun n _ _ h => DepthPadding.uamClass (B.atDepth n) (B.atDepth (n+1)) (B.padding) h

/-- The unbounded intrinsic relation uses the original empty-behaviour machines. -/
def Intrinsic (kind : Op → OperationKind) : State ops → State ops → Prop :=
  Step (fun n => UAMClasses.Step (UAM.emptyBehaviour ops n kind))

/-- The actual unbounded UAM contains intrinsic transitions and the global behaviour. -/
def UAMStep (B : Behaviour ops kind) (s t : State ops) : Prop := Intrinsic kind s t ∨ B.step s t

/-- Taking finite presentations adds no rules and loses no global compute steps. -/
theorem full_step_iff (B : Behaviour ops kind) (s t : State ops) :
    Step (RelationsOf B) s t ↔ UAMStep B s t := by
  constructor
  · rintro ⟨a,b,ha,hb,step⟩
    cases step with
    | @edge n x y h =>
      obtain ⟨u,v,hx,hy,h⟩ := h
      rcases h with intr | ext
      · left
        exact ⟨⟨n,x⟩,⟨n,y⟩,ha,hb,.edge ⟨u,v,hx,hy,Or.inl intr⟩⟩
      · right
        rw [hx] at ha
        rw [hy] at hb
        exact ha ▸ hb ▸ ext.1
  · intro h
    rcases h with intr | ext
    · obtain ⟨a,b,ha,hb,step⟩ := intr
      refine ⟨a,b,ha,hb,?_⟩
      cases step with
      | edge h =>
        obtain ⟨u,v,hu,hv,h⟩ := h
        rcases h with intr | impossible
        · exact .edge ⟨u,v,hu,hv,Or.inl intr⟩
        · exact False.elim impossible
    · obtain ⟨a,b,ha,hb,shape⟩ := B.compute ext
      refine ⟨a,b,ha,hb,?_⟩
      cases shape with
      | edge h =>
        obtain ⟨u,v,hu,hv,h⟩ := h
        apply At.edge
        refine ⟨u,v,hu,hv,Or.inr ⟨?_,h⟩⟩
        rw [hu] at ha
        rw [hv] at hb
        rw [← ha,← hb] at ext
        exact ext

/-- Final unbounded states are normal for the full machine. -/
theorem final_normal (B : Behaviour ops kind) {s t} (final : Final s) : ¬ UAMStep B s t := by
  intro step
  obtain ⟨a,b,ha,_,h⟩ := (full_step_iff B s t).mpr step
  rw [← ha] at final
  cases h with
  | edge h => exact UAMClasses.final_normal _ final h

/-- A machine on the actual unbounded state carrier. -/
def machine (B : Behaviour ops kind) : Machine (State ops) where
  step := UAMStep B
  final := Final
  final_normal := final_normal B

/-- Exact runs of the unbounded full machine have a common finite presentation. -/
theorem full_run_iff (B : Behaviour ops kind) {k s t} :
    Run (UAMStep B) k s t ↔ ∃ n, ∃ a b : DeepStateClass ops n,
      ofClass a = s ∧ ofClass b = t ∧ Run (UAMClasses.Step (B.atDepth n)) k a b := by
  constructor
  · intro run
    exact (finite_run_iff (full_preserved B)).mp
      (run_map id (fun h => (full_step_iff B _ _).mpr h) run)
  · intro run
    exact run_map id (fun h => (full_step_iff B _ _).mp h)
      ((finite_run_iff (full_preserved B)).mpr run)

/-- Full-UAM terminating observations preserve finality and exact cost. -/
theorem full_termination_iff (B : Behaviour ops kind) {k s} :
    (∃ t, Run (UAMStep B) k s t ∧ Final t) ↔
    ∃ n, ∃ a b : DeepStateClass ops n, ofClass a = s ∧
      Run (UAMClasses.Step (B.atDepth n)) k a b ∧ DeepStateClass.Final b := by
  constructor
  · rintro ⟨t,run,final⟩
    obtain ⟨n,a,b,ha,hb,run⟩ := (full_run_iff B).mp run
    rw [← hb] at final
    exact ⟨n,a,b,ha,run,final⟩
  · rintro ⟨n,a,b,ha,run,final⟩
    exact ⟨ofClass b,(full_run_iff B).mpr ⟨n,a,b,ha,rfl,run⟩,final⟩
end Hypernets.Linear.Unbounded
