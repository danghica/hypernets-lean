import Hypernets.Graph.DepthRoots

/-! Rootedness and refocusing of the actual unbounded machine. -/
namespace Hypernets.Linear.Unbounded
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- Rootedness descends because it is preserved and reflected by padding. -/
def Rooted (kind : Op → OperationKind) : State ops → Prop :=
  predicate (fun s => DeepStateClass.Rooted kind s.2) (fun s => DepthPadding.rooted_iff s.2)

theorem rooted_ofClass {n} (s : DeepStateClass ops n) :
    Rooted kind (ofClass s) ↔ DeepStateClass.Rooted kind s := Iff.rfl

/-- This quotient predicate is exactly reachability by search from an initial state. -/
theorem rooted_iff_initial_run (s : State ops) : Rooted kind s ↔
    ∃ a k, Initial a ∧ Run (Step (fun _ => DeepStateClass.Search kind)) k a s := by
  constructor
  · induction s using Quotient.inductionOn with
    | h s =>
      intro rooted
      obtain ⟨a,k,initial,run⟩ := (DeepStateClass.rooted_iff_initial_run s.2).mp rooted
      exact ⟨ofClass a,k,initial,(search_run_iff kind).mpr
        ⟨s.1,a,s.2,rfl,rfl,(run_steps_iff _).mpr run⟩⟩
  · rintro ⟨a,k,initial,run⟩
    obtain ⟨n,x,y,hx,hy,run⟩ := (search_run_iff kind).mp run
    rw [← hx] at initial
    rw [← hy]
    exact (DeepStateClass.rooted_iff_initial_run y).mpr
      ⟨x,k,initial,(run_steps_iff _).mp run⟩

/-- Refocusing is the paper's preservation condition on global extrinsic transitions. -/
def Behaviour.Refocusing (B : Behaviour ops kind) : Prop :=
  ∀ {s t}, Rooted kind s → B.step s t → Rooted kind t

/-- Global refocusing restricts to every finite presentation with no added premise. -/
theorem Behaviour.refocusingAt (B : Behaviour ops kind) (h : B.Refocusing) (n : Nat) :
    RefocusingStates kind (B.atDepth n).step := by
  intro s t root step
  exact h (s := ofClass (DeepStateClass.ofState s)) (t := ofClass (DeepStateClass.ofState t)) root step.1

/-- Intrinsic and extrinsic transitions both preserve the global rooted predicate. -/
theorem rooted_step (B : Behaviour ops kind) (h : B.Refocusing) {s t}
    (root : Rooted kind s) (step : UAMStep B s t) : Rooted kind t := by
  obtain ⟨a,b,ha,hb,step⟩ := (full_step_iff B s t).mpr step
  rw [← ha] at root
  rw [← hb]
  cases step with
  | edge step => exact UAMClasses.rooted_step _ (B.refocusingAt h _) root step

/-- Every full execution from an initial state remains rooted. -/
theorem initial_execution_rooted (B : Behaviour ops kind) (h : B.Refocusing)
    {k s t} (initial : Initial s) (run : (machine B).Steps k s t) : Rooted kind t := by
  have root : Rooted kind s := (rooted_iff_initial_run s).mpr ⟨s,0,initial,.nil s⟩
  clear initial
  induction run with
  | zero => exact root
  | cons step _ ih => exact ih (rooted_step B h root step)
end Hypernets.Linear.Unbounded
