import Hypernets.Graph.StationarySearch
import Hypernets.Graph.PlugSearchReflection
import Hypernets.Graph.PlugFocusInsertion

/-! The stationary criterion for a single ordinary shallow context. -/
namespace Hypernets.Linear.StationaryPlug
open Graph PlugSearchReflection StationarySearch
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
variable (C : Hypernet ops d [.term] []) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))

/-- Coordinate executions in the context survive arbitrary shallow filling. -/
theorem steps (name : Hole) (label : C.edgeLabel hole = primitiveLabel ops d (.hole name))
    {n p q} (run : (coordinateMachine C kind).Steps n p q) :
    (coordinateMachine (C.plug hole H) kind).Steps n
      (position C hole H p) (position C hole H q) := by
  induction run with
  | zero => exact .zero _
  | cons step _ ih => exact .cons (step.plug hole name label H) ih

/-- A one-way filling rules out a rooted term coordinate at a hole output. -/
theorem oneWay_target (one : OneWay H) {v : C.Vertex}
    (term : C.vertexLabel v = .term) (target : v ∈ C.target hole) :
    ¬ OperationReachable (C.plug hole H) (Net.Replacement.host C hole H v) := by
  obtain ⟨j,rfl⟩ := (C.mem_target_iff_port hole v).mp target
  intro root
  have localRoot := OneWayReplacement.extract C hole H (v := .output j) root
  have typed : H.vertexLabel (.output j) = .term := (C.targetPort_label hole j).symm.trans term
  exact (oneWay_iff.mp one) j typed localRoot

/-- The paper's immediate rewrite condition at every non-designated hole input. -/
def OtherInputsTrigger (entry : C.Vertex) : Prop :=
  ∀ v, v ∈ C.source hole → v ≠ entry → C.vertexLabel v = .term →
    ∃ q, SearchStep (C.plug hole H) kind (position C hole H (.search,v)) q ∧ q.1 = .rewrite

/-- Before the chosen search visit, no hole boundary can occur. Earlier visits
at the same input would create a cycle before a normal form; other inputs
immediately rewrite; one-wayness excludes returns through hole outputs. -/
theorem prefix_away (one : OneWay H) {entry : C.Vertex}
    (other : OtherInputsTrigger (kind := kind) C hole H entry)
    {n k r p z} (beforeRun : (coordinateMachine (C.plug hole H) kind).Steps n
      (.search,.input 0) (position C hole H p))
    (suffix : (coordinateMachine (C.plug hole H) kind).Steps k
      (position C hole H p) (position C hole H (.search,entry))) (positive : 0 < k)
    (finish : (coordinateMachine (C.plug hole H) kind).Steps r
      (position C hole H (.search,entry)) z) (rewrite : z.1 = .rewrite) :
    ¬ Boundary C hole p := by
  have props := run_properties beforeRun
  have typed : C.vertexLabel p.2 = .term :=
    (Net.Replacement.host_label C hole H p.2).symm.trans props.1
  rintro (enters | exits)
  · obtain ⟨mode,source⟩ := enters
    by_cases same : p.2 = entry
    · have eq : p = (.search,entry) := Prod.ext mode same
      rw [eq] at suffix
      have count := ((suffix.append finish).normal_unique (coordinateMachine_deterministic _ _)
        finish (rewrite_normal rewrite) (rewrite_normal rewrite)).1
      omega
    · obtain ⟨q,trigger,qmode⟩ := other p.2 source same typed
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
  · exact oneWay_target C hole H one typed exits.2 props.2

/-- The entire pre-rewrite prefix is a run in the unchanged context itself. -/
theorem extract_prefix (name : Hole)
    (label : C.edgeLabel hole = primitiveLabel ops d (.hole name)) (one : OneWay H) {entry : C.Vertex}
    (other : OtherInputsTrigger (kind := kind) C hole H entry)
    {n k r p z} (beforeRun : (coordinateMachine (C.plug hole H) kind).Steps n
      (.search,.input 0) (position C hole H p))
    (suffix : (coordinateMachine (C.plug hole H) kind).Steps k
      (position C hole H p) (position C hole H (.search,entry)))
    (finish : (coordinateMachine (C.plug hole H) kind).Steps r
      (position C hole H (.search,entry)) z) (rewrite : z.1 = .rewrite) :
    (coordinateMachine C kind).Steps k p (.search,entry) := by
  induction k generalizing n p with
  | zero =>
      have eq := suffix.zero_eq
      have same : p = (.search,entry) := Prod.ext (by simpa [position] using congrArg Prod.fst eq)
        (Net.Replacement.host_injective C hole H (congrArg Prod.snd eq))
      rw [same]
      exact .zero _
  | succ k ih =>
      have away := prefix_away C hole H one other beforeRun suffix (by omega) finish rewrite
      cases suffix with
      | cons first rest =>
          obtain ⟨q,step,eq⟩ := PlugSearchReflection.reflect C hole H name label first away
          rw [eq] at first rest
          exact .cons step (ih (beforeRun.append (.cons first (.zero _))) rest)

/-- The stationary criterion replays the search prefix with any replacement
family that retains the context's search interactions. -/
theorem replay (name : Hole)
    (label : C.edgeLabel hole = primitiveLabel ops d (.hole name)) (one : OneWay H) {entry : C.Vertex}
    (other : OtherInputsTrigger (kind := kind) C hole H entry)
    (K : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    {n} (run : (coordinateMachine (C.plug hole H) kind).Steps n (.search,.input 0)
      (position C hole H (.rewrite,entry))) :
    ∃ k, (coordinateMachine (C.plug hole K) kind).Steps k (.search,.input 0)
      (position C hole K (.search,entry)) := by
  obtain ⟨a,b,_,_,beforeRun,finish⟩ := SearchHistory.revisit run (by intro h; cases h)
  have contextRun := extract_prefix C hole H name label one other
    (n := 0) (p := (.search,.input 0)) (.zero _) beforeRun finish rfl
  exact ⟨a,steps C hole K name label contextRun⟩


/-- Simple contexts become focus-free and closed after a focus-free closed filling. -/
theorem filled_conditions (simple : SearchContexts.Simple C hole)
    (free : FocusFree H) (closed : HoleFree H) :
    FocusFree (C.plug hole H) ∧ HoleFree (C.plug hole H) := by
  constructor
  · intro e
    cases e with
    | inl e => exact simple.focusFree e.val
    | inr e => exact free e
  · intro h present
    obtain ⟨⟨e,p⟩,hp⟩ := (hasHole_iff_occurrences _ h).mp present
    cases e with
    | inl e => exact e.property (simple.only h ⟨e.val,p⟩ hp)
    | inr e => exact closed h ((hasHole_iff_occurrences H h).mpr ⟨⟨e,p⟩,hp⟩)

/-- Lemma 27 for ordinary shallow plugging and arbitrary actual endpoint names.
The source is a rewrite focus at one input of a one-way filling; the target is
a search focus at the same input of any focus-free closed replacement. -/
theorem rooted (simple : SearchContexts.Simple C hole)
    (hf : FocusFree H) (hc : HoleFree H) (one : OneWay H)
    (i : Fin ((alphabet ops d).signature.input (C.edgeLabel hole)).length)
    (term : H.vertexLabel (.input i) = .term)
    (other : OtherInputsTrigger (kind := kind) C hole H (C.sourcePort hole i))
    (K : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole))) (kf : FocusFree K) (kc : HoleFree K)
    {s t : State ops d}
    (left : Net.Iso (C.plug hole (PlugFocusInsertion.fragment C hole H i term .rewrite)) s.graph)
    (right : Net.Iso (C.plug hole (PlugFocusInsertion.fragment C hole K i term .search)) t.graph)
    (root : State.Rooted kind s) : State.Rooted kind t := by
  obtain ⟨hfree,hclosed⟩ := filled_conditions C hole H simple hf hc
  obtain ⟨kfree,kclosed⟩ := filled_conditions C hole K simple kf kc
  let p : TypedPosition (C.plug hole H) :=
    ⟨position C hole H (.rewrite,C.sourcePort hole i),
      (Net.Replacement.insert_label C hole H (.input i)).trans term⟩
  let q : TypedPosition (C.plug hole K) :=
    ⟨position C hole K (.search,C.sourcePort hole i),
      (Net.Replacement.insert_label C hole K (.input i)).trans term⟩
  have a : Focussed.Iso (p.realize hfree hclosed).focussed s.focussed :=
    Focussed.isoOfGraph ((PlugFocusInsertion.iso C hole H i term .rewrite).symm.trans left)
  have b : Focussed.Iso (q.realize kfree kclosed).focussed t.focussed :=
    Focussed.isoOfGraph ((PlugFocusInsertion.iso C hole K i term .search).symm.trans right)
  have leq : DeepStateClass.ofState (p.realize hfree hclosed) = DeepStateClass.ofState s :=
    Quotient.sound ⟨Focussed.DeepIso.ofIso a⟩
  have req : DeepStateClass.ofState (q.realize kfree kclosed) = DeepStateClass.ofState t :=
    Quotient.sound ⟨Focussed.DeepIso.ofIso b⟩
  have beforeRoot : State.Rooted kind (p.realize hfree hclosed) := by
    change DeepStateClass.Rooted kind _
    rw [leq]; exact root
  obtain ⟨n,run⟩ := (p.rooted_iff hfree hclosed).mp beforeRoot
  obtain ⟨k,trace⟩ := replay C hole H simple.hole simple.label one other K run
  have afterRoot : State.Rooted kind (q.realize kfree kclosed) :=
    q.realize_rooted kfree kclosed trace
  change DeepStateClass.Rooted kind _ at afterRoot ⊢
  rw [← req]
  exact afterRoot
end Hypernets.Linear.StationaryPlug
