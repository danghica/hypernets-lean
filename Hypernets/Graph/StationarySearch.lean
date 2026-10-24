import Hypernets.Graph.RootedCoordinates

/-! Stationary search-prefix replay, following Appendix C, Lemmas 27--28. -/
namespace Hypernets.Machine
variable {S : Type} {M : Machine S}
/-- Runs to normal forms in a deterministic machine have the same length and endpoint. -/
theorem Steps.normal_unique (det : M.Deterministic) {n m s t u}
    (left : M.Steps n s t) (right : M.Steps m s u)
    (tn : M.Normal t) (un : M.Normal u) : n = m ∧ t = u := by
  induction left generalizing m with
  | zero =>
      obtain ⟨z,eq⟩ := right.normal_eq tn
      exact ⟨z.symm,eq⟩
  | cons first tail ih =>
      cases right with
      | zero => exact False.elim (un _ first)
      | cons next rest =>
          have eq := det first next
          subst eq
          obtain ⟨length,endEq⟩ := ih rest tn
          exact ⟨by omega,endEq⟩
end Hypernets.Machine
namespace Hypernets.Linear.StationarySearch
open Graph ExpansionSearch
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

/-- Rooted coordinate runs preserve term typing and operation reachability. -/
theorem run_properties {G : Hypernet ops d [.term] []} {n p}
    (run : (coordinateMachine G kind).Steps n (.search,.input 0) p) :
    G.vertexLabel p.2 = .term ∧ OperationReachable G p.2 := by
  have propagate {k s t} (h : (coordinateMachine G kind).Steps k s t)
      (typed : G.vertexLabel s.2 = .term) (root : OperationReachable G s.2) :
      G.vertexLabel t.2 = .term ∧ OperationReachable G t.2 := by
    induction h with
    | zero => exact ⟨typed,root⟩
    | cons step _ ih => exact ih (step.preserves_term typed) (step.operationReachable root)
  exact propagate run rfl (OperationReachable.input (G := G) 0)

variable (C : Hypernet ops d [.term] [])
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- All changed hole fillings are one-way. Retained edges need no such property. -/
def OneWayHoles : Prop := ∀ e h, C.edgeLabel e = primitiveLabel ops d (.hole h) → OneWay (H e)

/-- At every other hole input, search immediately becomes rewrite, as in the
paper's stationary criterion. The designated input is allowed a longer search. -/
def OtherInputsTrigger (entry : C.Vertex) : Prop :=
  ∀ e h, C.edgeLabel e = primitiveLabel ops d (.hole h) → ∀ v, v ∈ C.source e →
    v ≠ entry → C.vertexLabel v = .term →
    ∃ q, SearchStep (C.expand H) kind (position C H (.search,v)) q ∧ q.1 = .rewrite

/-- A rewrite coordinate has no search successor. -/
theorem rewrite_normal {G : Hypernet ops d [.term] []} {p : SearchPosition G}
    (mode : p.1 = .rewrite) : (coordinateMachine G kind).Normal p := by
  intro q step
  have eq : p = (.rewrite,p.2) := Prod.ext mode rfl
  rw [eq] at step
  exact SearchStep.no_rewrite step

/-- Before the chosen search visit, no hole boundary can occur. Earlier visits
at the same input would create a cycle before a normal form; other inputs
immediately rewrite; one-wayness excludes returns through hole outputs. -/
theorem prefix_away (one : OneWayHoles C H) {entry : C.Vertex}
    (other : OtherInputsTrigger (kind := kind) C H entry)
    {n k r p z} (beforeRun : (coordinateMachine (C.expand H) kind).Steps n
      (.search,.input 0) (position C H p))
    (suffix : (coordinateMachine (C.expand H) kind).Steps k
      (position C H p) (position C H (.search,entry))) (positive : 0 < k)
    (finish : (coordinateMachine (C.expand H) kind).Steps r
      (position C H (.search,entry)) z) (rewrite : z.1 = .rewrite) :
    ¬ HoleBoundary C p := by
  have props := run_properties beforeRun
  have typed : C.vertexLabel p.2 = .term :=
    (Net.Expansion.host_label C H p.2).symm.trans props.1
  rintro ⟨e,h,label,enters | exits⟩
  · obtain ⟨mode,source⟩ := enters
    by_cases same : p.2 = entry
    · have eq : p = (.search,entry) := Prod.ext mode same
      rw [eq] at suffix
      have count := ((suffix.append finish).normal_unique (coordinateMachine_deterministic _ _)
        finish (rewrite_normal rewrite) (rewrite_normal rewrite)).1
      omega
    · obtain ⟨q,trigger,qmode⟩ := other e h label p.2 source same typed
      have eq : p = (.search,p.2) := Prod.ext mode rfl
      rw [← eq] at trigger
      cases k with
      | zero => omega
      | succ k =>
          have rest := suffix.drop_first (coordinateMachine_deterministic _ _) trigger
          have endEq := (rest.normal_eq (rewrite_normal qmode)).2
          have bad := congrArg Prod.fst endEq
          change q.1 = .search at bad
          cases qmode.symm.trans bad
  · exact ExpansionPaths.oneWay_target C H e (one e h label) typed exits.2 props.2

/-- The entire pre-rewrite prefix is a run in the unchanged context itself. -/
theorem extract_prefix (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    (one : OneWayHoles C H) {entry : C.Vertex}
    (other : OtherInputsTrigger (kind := kind) C H entry)
    {n k r p z} (beforeRun : (coordinateMachine (C.expand H) kind).Steps n
      (.search,.input 0) (position C H p))
    (suffix : (coordinateMachine (C.expand H) kind).Steps k
      (position C H p) (position C H (.search,entry)))
    (finish : (coordinateMachine (C.expand H) kind).Steps r
      (position C H (.search,entry)) z) (rewrite : z.1 = .rewrite) :
    (coordinateMachine C kind).Steps k p (.search,entry) := by
  induction k generalizing n p with
  | zero =>
      have eq := suffix.zero_eq
      have same : p = (.search,entry) := Prod.ext (by simpa [position] using congrArg Prod.fst eq)
        (Net.Expansion.host_injective C H (congrArg Prod.snd eq))
      rw [same]
      exact .zero _
  | succ k ih =>
      have away := prefix_away C H one other beforeRun suffix (by omega) finish rewrite
      cases suffix with
      | cons first rest =>
          obtain ⟨q,step,eq⟩ := (step_iff C H copies origins p away).mp first
          rw [eq] at first rest
          exact .cons step (ih (beforeRun.append (.cons first (.zero _))) rest)

/-- The stationary criterion replays the search prefix with any replacement
family that retains the context's search interactions. -/
theorem replay (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    (one : OneWayHoles C H) {entry : C.Vertex}
    (other : OtherInputsTrigger (kind := kind) C H entry)
    (K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (keeps : PreservesSearch C K)
    {n} (run : (coordinateMachine (C.expand H) kind).Steps n (.search,.input 0)
      (position C H (.rewrite,entry))) :
    ∃ k, (coordinateMachine (C.expand K) kind).Steps k (.search,.input 0)
      (position C K (.search,entry)) := by
  obtain ⟨a,b,_,_,beforeRun,finish⟩ := SearchHistory.revisit run (by intro h; cases h)
  have contextRun := extract_prefix C H copies origins one other
    (n := 0) (p := (.search,.input 0)) (.zero _) beforeRun finish rfl
  exact ⟨a,ExpansionSearch.steps C K keeps contextRun⟩

/-- Stationary rewriting preserves rootedness of actual realized states. Focus
freedom and hole freedom certify the endpoints; no rootedness of the reduct
or context-only execution is assumed. -/
theorem rooted (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    (one : OneWayHoles C H) (entry : C.Vertex) (term : C.vertexLabel entry = .term)
    (other : OtherInputsTrigger (kind := kind) C H entry)
    (K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (keeps : PreservesSearch C K)
    (hf : FocusFree (C.expand H)) (hc : HoleFree (C.expand H))
    (kf : FocusFree (C.expand K)) (kc : HoleFree (C.expand K))
    (root : State.Rooted kind ((TypedPosition.expand
      (⟨(.rewrite,entry),term⟩ : TypedPosition C) H).realize hf hc)) :
    State.Rooted kind ((TypedPosition.expand
      (⟨(.search,entry),term⟩ : TypedPosition C) K).realize kf kc) := by
  obtain ⟨n,run⟩ := (TypedPosition.rooted_iff _ hf hc).mp root
  obtain ⟨k,trace⟩ := replay C H copies origins one other K keeps run
  exact TypedPosition.realize_rooted kf kc _ trace

/-- Arbitrary recursive renaming of both actual endpoints does not change the
stationary rootedness conclusion. -/
theorem rooted_iso (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    (one : OneWayHoles C H) (entry : C.Vertex) (term : C.vertexLabel entry = .term)
    (other : OtherInputsTrigger (kind := kind) C H entry)
    (K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (keeps : PreservesSearch C K)
    (hf : FocusFree (C.expand H)) (hc : HoleFree (C.expand H))
    (kf : FocusFree (C.expand K)) (kc : HoleFree (C.expand K))
    {s t : State ops d}
    (left : Focussed.DeepIso ((TypedPosition.expand
      (⟨(.rewrite,entry),term⟩ : TypedPosition C) H).realize hf hc).focussed s.focussed)
    (right : Focussed.DeepIso ((TypedPosition.expand
      (⟨(.search,entry),term⟩ : TypedPosition C) K).realize kf kc).focussed t.focussed)
    (root : State.Rooted kind s) : State.Rooted kind t := by
  have leq : DeepStateClass.ofState ((TypedPosition.expand
      (⟨(.rewrite,entry),term⟩ : TypedPosition C) H).realize hf hc) = DeepStateClass.ofState s :=
    Quotient.sound ⟨left⟩
  have req : DeepStateClass.ofState ((TypedPosition.expand
      (⟨(.search,entry),term⟩ : TypedPosition C) K).realize kf kc) = DeepStateClass.ofState t :=
    Quotient.sound ⟨right⟩
  change DeepStateClass.Rooted kind _ at root ⊢
  rw [← req]
  apply rooted C H copies origins one entry term other K keeps hf hc kf kc
  change DeepStateClass.Rooted kind _
  rw [leq]
  exact root
end Hypernets.Linear.StationarySearch
