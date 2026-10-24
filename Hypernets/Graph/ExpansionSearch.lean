import Hypernets.Graph.DeepSpecimens
import Hypernets.Graph.ConcreteRefocusing

/-! Exact context search transport through simultaneous recursive fillings. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}

namespace ExpansionSearch
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- Only variables and operations participate in search; their copies suffice. -/
def PreservesSearch : Prop := ∀ e p, C.edgeLabel e = primitiveLabel ops d p →
  (p = .variable ∨ ∃ o, p = .operation o) → Nonempty (ExpansionPaths.CorollaCopy C H e)

/-- Host coordinates are embedded without changing the token mode. -/
def position (p : SearchPosition C) : SearchPosition (C.expand H) :=
  (p.1, Net.Expansion.host C H p.2)

/-- Ordered operation data survives expansion by a copy of its edge. -/
def operation (a : SearchOperation C) (copy : ExpansionPaths.CorollaCopy C H a.edge) :
    SearchOperation (C.expand H) where
  edge := ⟨a.edge, copy.edge⟩
  operation := a.operation
  label := copy.label.trans a.label
  source := Net.Expansion.host C H a.source
  arguments := a.arguments.map (Net.Expansion.host C H)
  thunks := a.thunks.map (Net.Expansion.host C H)
  source_eq := by rw [ExpansionPaths.copy_source_eq C H copy, a.source_eq]; rfl
  target_eq := by rw [ExpansionPaths.copy_target_eq C H copy, a.target_eq, List.map_append]
  arity := by simp [a.arity]

theorem operation_enter (a : SearchOperation C) (copy : ExpansionPaths.CorollaCopy C H a.edge)
    (kind : Op → OperationKind) :
    (operation C H a copy).enter kind = position C H (a.enter kind) := by
  cases h : a.arguments <;> simp [SearchOperation.enter, operation, position, h]

theorem operation_resume (a : SearchOperation C) (copy : ExpansionPaths.CorollaCopy C H a.edge)
    (kind : Op → OperationKind) (i : Nat) :
    (operation C H a copy).resume kind i = position C H (a.resume kind i) := by
  simp only [SearchOperation.resume, operation, List.getElem?_map]
  cases a.arguments[i+1]? <;> rfl

/-- Every context step survives, independently of the contents of all holes. -/
theorem step (copies : PreservesSearch C H) {kind : Op → OperationKind} {p q}
    (h : SearchStep C kind p q) :
    SearchStep (C.expand H) kind (position C H p) (position C H q) := by
  cases h with
  | trigger e v label source =>
      obtain ⟨copy⟩ := copies e .variable label (.inl rfl)
      apply SearchStep.trigger (G := C.expand H) ⟨e,copy.edge⟩ (Net.Expansion.host C H v)
      · exact copy.label.trans label
      · rw [ExpansionPaths.copy_source_eq C H copy, source]; rfl
  | enter a =>
      obtain ⟨copy⟩ := copies a.edge (.operation a.operation) a.label (.inr ⟨_,rfl⟩)
      rw [← operation_enter C H a copy kind]
      exact SearchStep.enter (kind := kind) (operation C H a copy)
  | resume a i v arg =>
      obtain ⟨copy⟩ := copies a.edge (.operation a.operation) a.label (.inr ⟨_,rfl⟩)
      have mapped : (operation C H a copy).arguments[i]? = some (Net.Expansion.host C H v) := by
        simp [operation, List.getElem?_map, arg]
      simpa only [operation_resume, position] using
        SearchStep.resume (kind := kind) (operation C H a copy) i _ mapped

/-- Once a context step exists, every filled-graph successor is exactly its image. -/
theorem successor_unique (copies : PreservesSearch C H) {kind : Op → OperationKind} {p q r}
    (h : SearchStep C kind p q)
    (other : SearchStep (C.expand H) kind (position C H p) r) : r = position C H q :=
  SearchStep.deterministic other (step C H copies h)

end ExpansionSearch

/-- Recursive paired fillings retain every original variable and operation. -/
theorem DeepFillingEdge.search_copies {T : LayeredPreTemplate ops}
    {C : Hypernet ops d I O} {H K e} (cert : DeepFillingEdge T C H K e)
    {p : Primitive Op} (label : C.edgeLabel e = primitiveLabel ops d p)
    (search : p = .variable ∨ ∃ o, p = .operation o) :
    Nonempty (ExpansionPaths.CorollaCopy C H e) ∧ Nonempty (ExpansionPaths.CorollaCopy C K e) := by
  cases cert with
  | retained l r => exact ⟨⟨l⟩,⟨r⟩⟩
  | filled h hole rel =>
      have eq := primitiveLabel_injective d (label.symm.trans hole)
      rcases search with rfl | ⟨o,rfl⟩ <;> cases eq
  | boxed b box inner l r => cases label.symm.trans box

/-- Both sides admit the same exact context search steps. -/
theorem deepFilling_preservesSearch {T : LayeredPreTemplate ops}
    {C : Hypernet ops d I O} {H K} (edges : ∀ e, DeepFillingEdge T C H K e) :
    ExpansionSearch.PreservesSearch C H ∧ ExpansionSearch.PreservesSearch C K :=
  ⟨fun e _ label h => ((edges e).search_copies label h).1,
   fun e _ label h => ((edges e).search_copies label h).2⟩

/-- Search on coordinates, including open contexts; final means return at an input. -/
def coordinateMachine (C : Hypernet ops d I O) (kind : Op → OperationKind) :
    Machine (SearchPosition C) where
  step := SearchStep C kind
  final p := p.1 = .backtrack ∧ p.2.IsInput
  final_normal := by
    intro p q final h
    obtain ⟨mode, input⟩ := final
    have eq : p = (.backtrack, p.2) := Prod.ext mode rfl
    rw [eq] at h
    exact SearchStep.final_no_step input h

theorem coordinateMachine_deterministic (C : Hypernet ops d I O) (kind : Op → OperationKind) :
    (coordinateMachine C kind).Deterministic := by
  intro s t u left right
  exact SearchStep.deterministic left right

namespace ExpansionSearch
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- All finite context executions transport with their exact length. -/
theorem steps (copies : PreservesSearch C H) {kind : Op → OperationKind} {n p q}
    (run : (coordinateMachine C kind).Steps n p q) :
    (coordinateMachine (C.expand H) kind).Steps n (position C H p) (position C H q) := by
  induction run with
  | zero => exact .zero _
  | cons first _ ih => exact .cons (step C H copies first) ih

/-- Successful return at the boundary is preserved and reflected by the host map. -/
theorem final_iff (kind : Op → OperationKind) (p : SearchPosition C) :
    (coordinateMachine (C.expand H) kind).final (position C H p) ↔
      (coordinateMachine C kind).final p := by
  rcases p with ⟨mode,v⟩
  cases v <;> rfl

/-- A completed context execution fixes the exact time and result of every
successful filled-graph execution, even if its steps are presented independently. -/
theorem final_run_unique (copies : PreservesSearch C H) {kind : Op → OperationKind}
    {n m p q r} (contextRun : (coordinateMachine C kind).Steps n p q)
    (contextFinal : (coordinateMachine C kind).final q)
    (filledRun : (coordinateMachine (C.expand H) kind).Steps m (position C H p) r)
    (filledFinal : (coordinateMachine (C.expand H) kind).final r) :
    m = n ∧ r = position C H q :=
  filledRun.final_unique (coordinateMachine_deterministic _ _) (steps C H copies contextRun)
    filledFinal ((final_iff C H kind q).mpr contextFinal)

end ExpansionSearch

namespace TypedPosition
variable {C : Hypernet ops d [.term] []}

/-- Term-typed coordinates remain term-typed under simultaneous filling. -/
def expand (p : TypedPosition C)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) : TypedPosition (C.expand H) :=
  ⟨ExpansionSearch.position C H p.val, (Net.Expansion.host_label C H p.val.2).trans p.property⟩

/-- Expanding an initial coordinate leaves it at the same boundary input. -/
theorem expand_initial
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) :
    (initial C).expand H = initial (C.expand H) := rfl

/-- Every coordinate execution on a closed focus-free graph gives an execution
of actual state classes, with exactly the same number of search steps. -/
theorem realize_steps (fg : FocusFree C) (hg : HoleFree C) {kind : Op → OperationKind}
    {n} (p q : TypedPosition C) (run : (coordinateMachine C kind).Steps n p.val q.val) :
    (DeepStateClass.searchMachine kind).Steps n
      (DeepStateClass.ofState (p.realize fg hg)) (DeepStateClass.ofState (q.realize fg hg)) := by
  generalize hp : p.val = pv at run
  generalize hq : q.val = qv at run
  induction run generalizing p q with
  | zero =>
      have eq : p = q := Subtype.ext (hp.trans hq.symm)
      subst q
      exact .zero _
  | @cons n s t v first tail ih =>
      let mid : TypedPosition C := ⟨t, first.preserves_term (hp ▸ p.property)⟩
      apply Machine.Steps.cons (t := DeepStateClass.ofState (mid.realize fg hg))
      · apply State.search_deepSearch
        apply p.search_realize mid fg hg
        exact hp ▸ first
      · exact ih mid q rfl hq

/-- A run from the initial input proves rootedness of its actual realization
on a closed focus-free graph. -/
theorem realize_rooted (fg : FocusFree C) (hg : HoleFree C) {kind : Op → OperationKind}
    {n} (p : TypedPosition C)
    (run : (coordinateMachine C kind).Steps n (initial C).val p.val) :
    State.Rooted kind (p.realize fg hg) := by
  apply (DeepStateClass.rooted_iff_initial_run _).mpr
  exact ⟨DeepStateClass.ofState ((initial C).realize fg hg),n, initial_realize fg hg, (initial C).realize_steps fg hg p run⟩

end TypedPosition

namespace ExpansionSearch
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- Search enters a hole at a source, or returns from a hole at a target. -/
def HoleBoundary (p : SearchPosition C) : Prop := ∃ e h,
  C.edgeLabel e = primitiveLabel ops d (.hole h) ∧
  ((p.1 = .search ∧ p.2 ∈ C.source e) ∨ (p.1 = .backtrack ∧ p.2 ∈ C.target e))

/-- An expanded edge incident from a host vertex is owned by an edge incident
from that original vertex. Inserted internal vertices cannot coincide with it. -/
theorem source_owner_mem {e : C.Edge} {x : (H e).Edge} {v : C.Vertex}
    (mem : Net.Expansion.host C H v ∈ (C.expand H).source ⟨e,x⟩) : v ∈ C.source e := by
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
  cases w with
  | internal a => exact False.elim (Net.Expansion.host_ne_internal C H v e a eq.symm)
  | input i =>
      exact (Net.Expansion.host_injective C H eq) ▸ C.sourcePort_mem e i
  | output i => exact False.elim ((H e).source_not_output hw trivial)

theorem target_owner_mem {e : C.Edge} {x : (H e).Edge} {v : C.Vertex}
    (mem : Net.Expansion.host C H v ∈ (C.expand H).target ⟨e,x⟩) : v ∈ C.target e := by
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
  cases w with
  | internal a => exact False.elim (Net.Expansion.host_ne_internal C H v e a eq.symm)
  | output i => exact (Net.Expansion.host_injective C H eq) ▸ C.targetPort_mem e i
  | input i => exact False.elim ((H e).target_not_input hw trivial)

/-- Read an operation in a retained copy back to its original ordered operation. -/
theorem operation_readback (a : SearchOperation (C.expand H))
    (copy : ExpansionPaths.CorollaCopy C H a.edge.1) :
    ∃ b : SearchOperation C, b.edge = a.edge.1 ∧
      a.source = Net.Expansion.host C H b.source ∧
      a.arguments = b.arguments.map (Net.Expansion.host C H) := by
  have lab : C.edgeLabel a.edge.1 = primitiveLabel ops d (.operation a.operation) := by
    have same := copy.only a.edge.2
    exact copy.label.symm.trans (same ▸ a.label)
  obtain ⟨old,edge,_⟩ := SearchOperation.exists_view a.edge.1 a.operation lab
  let b : SearchOperation C := { old with
    edge := a.edge.1
    label := edge ▸ old.label
    source_eq := edge ▸ old.source_eq
    target_eq := edge ▸ old.target_eq }
  have eq : a.edge = (operation C H b copy).edge :=
    congrArg (Sigma.mk a.edge.1) (copy.only a.edge.2)
  obtain ⟨_,src,args⟩ := a.data_unique (operation C H b copy) eq
  exact ⟨b,rfl,src,args⟩

end ExpansionSearch

/-- An operation or variable inside a recursive filling is either the retained
original edge, or belongs to a filled hole. A rebuilt box is never such a redex. -/
theorem DeepFillingEdge.search_origin {T : LayeredPreTemplate ops}
    {C : Hypernet ops d I O} {H K e} (cert : DeepFillingEdge T C H K e)
    (x : (H e).Edge) {p : Primitive Op}
    (label : (H e).edgeLabel x = primitiveLabel ops d p)
    (_search : p = .variable ∨ ∃ o, p = .operation o) :
    Nonempty (ExpansionPaths.CorollaCopy C H e) ∨
      ∃ h, C.edgeLabel e = primitiveLabel ops d (.hole h) := by
  cases cert with
  | retained l r => exact .inl ⟨l⟩
  | filled h hole rel => exact .inr ⟨h,hole⟩
  | boxed b box inner l r =>
      have eq := (l.only x) ▸ label
      have bad := l.edge_label.symm.trans eq
      cases bad

namespace ExpansionSearch
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- Every participating edge of a filling comes from a retained copy or a hole. -/
def SearchOrigins : Prop := ∀ e (x : (H e).Edge) p,
  (H e).edgeLabel x = primitiveLabel ops d p →
  (p = .variable ∨ ∃ o, p = .operation o) →
  Nonempty (ExpansionPaths.CorollaCopy C H e) ∨
    ∃ h, C.edgeLabel e = primitiveLabel ops d (.hole h)

/-- Exhaustive one-step classification at a host coordinate: a context move,
or entry/exit at an original shallow hole. Deep box changes cause no extra case. -/
theorem reflect_or_boundary (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    {kind : Op → OperationKind} (p : SearchPosition C) {q}
    (step : SearchStep (C.expand H) kind (position C H p) q) :
    (∃ r, SearchStep C kind p r ∧ q = position C H r) ∨ HoleBoundary C p := by
  have finish (r) (h : SearchStep C kind p r) :
      (∃ r, SearchStep C kind p r ∧ q = position C H r) ∨ HoleBoundary C p :=
    .inl ⟨r,h,successor_unique C H copies h step⟩
  generalize hp : position C H p = start at step
  cases step with
  | trigger e v label source =>
      have mem : p.2 ∈ C.source e.1 := source_owner_mem C H (by
        change Net.Expansion.host C H p.2 ∈ (C.expand H).source e
        rw [source, (Prod.mk.inj hp).2]; simp)
      rcases origins e.1 e.2 _ label (.inl rfl) with copy | ⟨hole,hl⟩
      · obtain ⟨copy⟩ := copy
        have lab : C.edgeLabel e.1 = primitiveLabel ops d .variable :=
          copy.label.symm.trans ((copy.only e.2) ▸ label)
        have len : (C.source e.1).length = 1 := by
          rw [C.source_length,lab]; cases d <;> rfl
        obtain ⟨w,hw⟩ := List.length_eq_one_iff.mp len
        have eq : p.2 = w := List.mem_singleton.mp (hw ▸ mem)
        have pm : p = (.search,p.2) := Prod.ext (Prod.mk.inj hp).1 rfl
        apply finish (.rewrite,p.2)
        rw [pm]
        exact .trigger e.1 p.2 lab (hw.trans (congrArg List.singleton eq.symm))
      · exact .inr ⟨e.1,hole,hl,.inl ⟨(Prod.mk.inj hp).1,mem⟩⟩
  | enter a =>
      have mem : p.2 ∈ C.source a.edge.1 := source_owner_mem C H (by
        change Net.Expansion.host C H p.2 ∈ (C.expand H).source a.edge
        rw [a.source_eq, (Prod.mk.inj hp).2]; simp)
      rcases origins a.edge.1 a.edge.2 _ a.label (.inr ⟨_,rfl⟩) with copy | ⟨hole,hl⟩
      · obtain ⟨copy⟩ := copy
        obtain ⟨b,_,src,_⟩ := operation_readback C H a copy
        have same : p.2 = b.source := Net.Expansion.host_injective C H ((Prod.mk.inj hp).2.trans src)
        have eq : p = (.search,b.source) := Prod.ext (Prod.mk.inj hp).1 same
        apply finish (b.enter kind)
        rw [eq]
        exact .enter b
      · exact .inr ⟨a.edge.1,hole,hl,.inl ⟨(Prod.mk.inj hp).1,mem⟩⟩
  | resume a i v arg =>
      have mem : p.2 ∈ C.target a.edge.1 := target_owner_mem C H (by
        change Net.Expansion.host C H p.2 ∈ (C.expand H).target a.edge
        rw [(Prod.mk.inj hp).2]
        exact a.argument_mem (List.mem_of_getElem? arg))
      rcases origins a.edge.1 a.edge.2 _ a.label (.inr ⟨_,rfl⟩) with copy | ⟨hole,hl⟩
      · obtain ⟨copy⟩ := copy
        obtain ⟨b,_,_,args⟩ := operation_readback C H a copy
        have mapped : (b.arguments[i]?).map (Net.Expansion.host C H) =
            (some p.2).map (Net.Expansion.host C H) := by
          rw [← List.getElem?_map, ← args, arg]
          exact congrArg some (Prod.mk.inj hp).2.symm
        have original := Option.map_injective (fun _ _ h => Net.Expansion.host_injective C H h) mapped
        have eq : p = (.backtrack,p.2) := Prod.ext (Prod.mk.inj hp).1 rfl
        apply finish (b.resume kind i)
        rw [eq]
        exact .resume b i p.2 original
      · exact .inr ⟨a.edge.1,hole,hl,.inr ⟨(Prod.mk.inj hp).1,mem⟩⟩

/-- Away from hole boundaries, search is exactly the transported context relation. -/
theorem step_iff (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    {kind : Op → OperationKind} (p : SearchPosition C) (away : ¬ HoleBoundary C p) {q} :
    SearchStep (C.expand H) kind (position C H p) q ↔
      ∃ r, SearchStep C kind p r ∧ q = position C H r := by
  constructor
  · intro h
    rcases reflect_or_boundary C H copies origins p h with good | bad
    · exact good
    · exact False.elim (away bad)
  · rintro ⟨r,h,rfl⟩
    exact step C H copies h

/-- If a forward-closed region avoids all hole boundaries, every expanded run
starting in that region is exactly a context run of the same length. -/
theorem steps_reflect (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    {kind : Op → OperationKind} (region : SearchPosition C → Prop)
    (away : ∀ p, region p → ¬ HoleBoundary C p)
    (closed : ∀ {p q}, region p → SearchStep C kind p q → region q)
    {n p q} (inside : region p)
    (run : (coordinateMachine (C.expand H) kind).Steps n (position C H p) q) :
    ∃ r, (coordinateMachine C kind).Steps n p r ∧ q = position C H r ∧ region r := by
  induction n generalizing p q with
  | zero => exact ⟨p,.zero _,run.zero_eq.symm,inside⟩
  | succ n ih =>
      cases run with
      | cons first tail =>
          obtain ⟨mid,step,eq⟩ := (step_iff C H copies origins p (away p inside)).mp first
          rw [eq] at tail
          obtain ⟨last,rest,eq,member⟩ := ih (closed inside step) tail
          exact ⟨last,.cons step rest,eq,member⟩

/-- When all holes lie strictly inside boxes, outer search is completely
preserved and reflected, including exact successful execution lengths. -/
theorem final_runs_iff (copies : PreservesSearch C H) (origins : SearchOrigins C H)
    (noShallow : ∀ e h, C.edgeLabel e ≠ primitiveLabel ops d (.hole h))
    (kind : Op → OperationKind) (n : Nat) (p : SearchPosition C) :
    (∃ q, (coordinateMachine (C.expand H) kind).Steps n (position C H p) q ∧
      (coordinateMachine (C.expand H) kind).final q) ↔
    ∃ r, (coordinateMachine C kind).Steps n p r ∧ (coordinateMachine C kind).final r := by
  constructor
  · rintro ⟨q,run,final⟩
    have away : ∀ p : SearchPosition C, True → ¬ HoleBoundary C p := by
      rintro p _ ⟨e,h,label,_⟩
      exact noShallow e h label
    obtain ⟨r,run,eq,_⟩ := steps_reflect C H copies origins (fun _ => True) away
      (fun _ _ => trivial) trivial run
    exact ⟨r,run,(final_iff C H kind r).mp (eq ▸ final)⟩
  · rintro ⟨r,run,final⟩
    exact ⟨position C H r,steps C H copies run,(final_iff C H kind r).mpr final⟩

end ExpansionSearch

/-- Recursive paired fillings satisfy the redex-origin condition on both sides. -/
theorem deepFilling_searchOrigins {T : LayeredPreTemplate ops}
    {C : Hypernet ops d I O} {H K} (edges : ∀ e, DeepFillingEdge T C H K e) :
    ExpansionSearch.SearchOrigins C H ∧ ExpansionSearch.SearchOrigins C K := by
  constructor
  · exact fun e x _ label h => (edges e).search_origin x label h
  · intro e x p label _
    cases edges e with
    | retained l r => exact .inl ⟨r⟩
    | filled h hole rel => exact .inr ⟨h,hole⟩
    | boxed b box inner l r =>
        have eq := (r.only x) ▸ label
        have bad := r.edge_label.symm.trans eq
        cases bad

namespace ExpansionSearch
variable {T : LayeredPreTemplate ops} {C : Hypernet ops d [.term] []}
    {H K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))}

/-- A paired filling supplies actual closed states at every typed host coordinate. -/
noncomputable def filledState (edges : ∀ e, DeepFillingEdge T C H K e)
    (free : FocusFree C) (closed : HoleFree (C.expand H)) (p : TypedPosition C) : State ops d :=
  (p.expand H).realize ((DeepFilling.expand C H K edges).focusFree free).1 closed

/-- Context executions give actual paired executions with exactly equal counts. -/
theorem paired_steps (edges : ∀ e, DeepFillingEdge T C H K e)
    (free : FocusFree C) (lh : HoleFree (C.expand H)) (rh : HoleFree (C.expand K))
    {kind : Op → OperationKind} {n} (p q : TypedPosition C)
    (run : (coordinateMachine C kind).Steps n p.val q.val) :
    (DeepStateClass.searchMachine kind).Steps n
      (DeepStateClass.ofState (filledState edges free lh p))
      (DeepStateClass.ofState (filledState edges free lh q)) ∧
    (DeepStateClass.searchMachine kind).Steps n
      (DeepStateClass.ofState ((p.expand K).realize ((DeepFilling.expand C H K edges).focusFree free).2 rh))
      (DeepStateClass.ofState ((q.expand K).realize ((DeepFilling.expand C H K edges).focusFree free).2 rh)) := by
  have preserves := deepFilling_preservesSearch edges
  exact ⟨(p.expand H).realize_steps _ _ (q.expand H) (steps C H preserves.1 run),
    (p.expand K).realize_steps _ _ (q.expand K) (steps C K preserves.2 run)⟩

/-- Filling a context-only initial run yields rooted actual states on both sides. -/
theorem paired_rooted (edges : ∀ e, DeepFillingEdge T C H K e)
    (free : FocusFree C) (lh : HoleFree (C.expand H)) (rh : HoleFree (C.expand K))
    {kind : Op → OperationKind} {n} (q : TypedPosition C)
    (run : (coordinateMachine C kind).Steps n (TypedPosition.initial C).val q.val) :
    State.Rooted kind (filledState edges free lh q) ∧
    State.Rooted kind ((q.expand K).realize ((DeepFilling.expand C H K edges).focusFree free).2 rh) := by
  have preserves := deepFilling_preservesSearch edges
  exact ⟨(q.expand H).realize_rooted _ _ (steps C H preserves.1 run),
    (q.expand K).realize_rooted _ _ (steps C K preserves.2 run)⟩

/-- Equal-length executions from a common recursive state class have the same
endpoint. Thus paired traversal does not depend on choosing the constructed run. -/
theorem state_run_unique {kind : Op → OperationKind} {n} {s t u : DeepStateClass ops d}
    (left : (DeepStateClass.searchMachine kind).Steps n s t)
    (right : (DeepStateClass.searchMachine kind).Steps n s u) : t = u := by
  induction left generalizing u with
  | zero => exact right.zero_eq
  | cons first tail ih =>
      cases right with
      | cons other rest =>
          have eq := DeepStateClass.search_deterministic first other
          subst eq
          exact ih rest

/-- An independently supplied actual-state execution of a context trace's length
must reach the same state class as the transported trace. -/
theorem actual_run_endpoint (edges : ∀ e, DeepFillingEdge T C H K e)
    (free : FocusFree C) (lh : HoleFree (C.expand H)) (rh : HoleFree (C.expand K))
    {kind : Op → OperationKind} {n} (p q : TypedPosition C)
    (contextRun : (coordinateMachine C kind).Steps n p.val q.val) {target}
    (actualRun : (DeepStateClass.searchMachine kind).Steps n
      (DeepStateClass.ofState (filledState edges free lh p)) target) :
    target = DeepStateClass.ofState (filledState edges free lh q) :=
  state_run_unique actualRun (paired_steps edges free lh rh p q contextRun).1

end ExpansionSearch
end Hypernets.Linear
