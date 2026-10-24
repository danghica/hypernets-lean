import Hypernets.Graph.UnboundedStates

/-! Exact finite-run witnesses in the union of finite-depth state spaces. -/
namespace Hypernets.Linear.Unbounded
variable {Op : Type} {ops : Operations Op}

/-- A family of concrete fixed-depth transition relations. -/
abbrev Relations (ops : Operations Op) := ∀ n, DeepStateClass ops n → DeepStateClass ops n → Prop

/-- One finite presentation of a transition has a common depth for its endpoints. -/
inductive At (R : Relations ops) : Stage ops → Stage ops → Prop where
  | edge {n} {s t : DeepStateClass ops n} : R n s t → At R ⟨n,s⟩ ⟨n,t⟩

/-- Compatibility required from a concrete rule, rather than assumed of all rules. -/
def Preserved (R : Relations ops) : Prop := ∀ n s t, R n s t →
  R (n+1) (DepthPadding.stateClass s) (DepthPadding.stateClass t)

theorem at_next {R : Relations ops} (h : Preserved R) {s t} (step : At R s t) :
    At R (next s) (next t) := by
  cases step with | edge step => exact .edge (h _ _ _ step)

theorem at_advance {R : Relations ops} (h : Preserved R) (k) {s t} (step : At R s t) :
    At R (advance k s) (advance k t) := by
  induction k with
  | zero => exact step
  | succ k ih => exact at_next h ih

/-- A step in the unbounded carrier is witnessed by an actual finite-depth step. -/
def Step (R : Relations ops) (s t : State ops) : Prop :=
  ∃ a b, ofStage a = s ∧ ofStage b = t ∧ At R a b

/-- Runs count transitions exactly; zero steps identifies its two endpoints. -/
inductive Run {S : Type u} (r : S → S → Prop) : Nat → S → S → Prop where
  | nil (s) : Run r 0 s s
  | cons {k s t u} : r s t → Run r k t u → Run r (k+1) s u

theorem run_map {S : Type u} {T : Type v} {r : S → S → Prop} {q : T → T → Prop}
    (f : S → T) (h : ∀ {s t}, r s t → q (f s) (f t)) {k s t} (run : Run r k s t) :
    Run q k (f s) (f t) := by
  induction run with
  | nil => exact .nil _
  | cons step _ ih => exact .cons (h step) ih

theorem run_advance {R : Relations ops} (h : Preserved R) (i) {k s t}
    (run : Run (At R) k s t) : Run (At R) k (advance i s) (advance i t) :=
  run_map (advance i) (at_advance h i) run

/-- Every bounded execution projects with exactly the same number of transitions. -/
theorem project_run {R : Relations ops} {k s t} (run : Run (At R) k s t) :
    Run (Step R) k (ofStage s) (ofStage t) :=
  run_map ofStage (fun {a b} step => ⟨a,b,rfl,rfl,step⟩) run

/-- A finite unbounded execution has a single common-depth witness. At a join,
raise both pieces until their middle presentations coincide, preserving counts. -/
theorem lift_run {R : Relations ops} (h : Preserved R) {k s t}
    (run : Run (Step R) k s t) :
    ∃ a b, ofStage a = s ∧ ofStage b = t ∧ Run (At R) k a b := by
  induction run with
  | nil s =>
      induction s using Quotient.inductionOn with
      | h s => exact ⟨s,s,rfl,rfl,.nil s⟩
  | cons step _ ih =>
      obtain ⟨a,b,ha,hb,ab⟩ := step
      obtain ⟨c,e,hc,he,ce⟩ := ih
      obtain ⟨i,j,eq⟩ := Quotient.exact (hb.trans hc.symm)
      refine ⟨advance i a,advance j e,(ofStage_advance i a).trans ha,
        (ofStage_advance j e).trans he,?_⟩
      have ab := at_advance h i ab
      rw [eq] at ab
      exact .cons ab (run_advance h j ce)

/-- Every edge, hence every finite run, retains one common depth. -/
theorem at_depth {R : Relations ops} {s t} (step : At R s t) : s.1 = t.1 := by
  cases step
  rfl

theorem run_depth {R : Relations ops} {k s t} (run : Run (At R) k s t) : s.1 = t.1 := by
  induction run with
  | nil => rfl
  | cons step _ ih => exact (at_depth step).trans ih

/-- Extract the original fixed-depth relation from a staged edge. -/
theorem at_same_depth {R : Relations ops} {n} {s t : DeepStateClass ops n}
    (step : At R ⟨n,s⟩ ⟨n,t⟩) : R n s t := by
  cases step with | edge h => exact h

/-- A staged run is an actual run of the original relation at its source depth. -/
theorem run_same_depth {R : Relations ops} {k n} {s t : DeepStateClass ops n}
    (run : Run (At R) k ⟨n,s⟩ ⟨n,t⟩) : Run (R n) k s t := by
  generalize hs : (⟨n,s⟩ : Stage ops) = a at run
  generalize ht : (⟨n,t⟩ : Stage ops) = b at run
  induction run generalizing n s t with
  | nil a =>
      have eq := hs.trans ht.symm
      have eq : s = t := eq_of_heq (Sigma.mk.inj eq).2
      subst t
      exact .nil s
  | @cons k a b c edge tail ih =>
      subst a
      obtain ⟨m,b⟩ := b
      have depth : n = m := at_depth edge
      subst m
      exact .cons (at_same_depth edge) (ih rfl ht)

/-- Exact finite-run adequacy, with a depth chosen after the entire run is known. -/
theorem finite_run_iff {R : Relations ops} (h : Preserved R) {k s t} :
    Run (Step R) k s t ↔ ∃ n, ∃ (a b : DeepStateClass ops n),
      ofClass a = s ∧ ofClass b = t ∧ Run (R n) k a b := by
  constructor
  · intro run
    obtain ⟨⟨n,a⟩,⟨m,b⟩,ha,hb,run⟩ := lift_run h run
    have depth : n = m := run_depth run
    subst m
    exact ⟨n,a,b,ha,hb,run_same_depth run⟩
  · rintro ⟨n,a,b,ha,hb,run⟩
    rw [← ha,← hb]
    exact project_run (run_map (fun a => (⟨n,a⟩ : Stage ops)) (fun step => At.edge step) run)

/-- The five search rules satisfy the required compatibility by the concrete proof. -/
theorem search_preserved (kind : Op → OperationKind) :
    Preserved (fun _ => DeepStateClass.Search (ops := ops) kind) :=
  fun _ s t h => (DepthPadding.class_search_iff kind s t).mpr h

/-- An unbounded search run is precisely a bounded search run at some finite depth. -/
theorem search_run_iff (kind : Op → OperationKind) {k s t} :
    Run (Step (fun _ => DeepStateClass.Search (ops := ops) kind)) k s t ↔
      ∃ n, ∃ (a b : DeepStateClass ops n), ofClass a = s ∧ ofClass b = t ∧
        Run (DeepStateClass.Search (ops := ops) kind) k a b := finite_run_iff (search_preserved kind)
/-- Termination observations retain both finality and their exact execution cost. -/
theorem terminating_run_iff {R : Relations ops} (h : Preserved R) {k s} :
    (∃ t, Run (Step R) k s t ∧ Final t) ↔
    ∃ n, ∃ (a b : DeepStateClass ops n), ofClass a = s ∧
      Run (R n) k a b ∧ DeepStateClass.Final b := by
  constructor
  · rintro ⟨t,run,final⟩
    obtain ⟨n,a,b,ha,hb,run⟩ := (finite_run_iff h).mp run
    rw [← hb] at final
    exact ⟨n,a,b,ha,run,final⟩
  · rintro ⟨n,a,b,ha,run,final⟩
    exact ⟨ofClass b,(finite_run_iff h).mpr ⟨n,a,b,ha,rfl,run⟩,final⟩
end Hypernets.Linear.Unbounded
