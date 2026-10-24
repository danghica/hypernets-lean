import Hypernets.Graph.Focused

/-! The five search rules of Fig. 9(a–e), in coordinates on the underlying
hypernet. StateSearch lifts these to explicit states; local-rewrite adequacy remains open. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- The operation partition is a parameter of the UAM (§5.1). -/
inductive OperationKind where
  | passive
  | active
  deriving DecidableEq

/-- Completing arguments returns a value or triggers computation. -/
def OperationKind.finish : OperationKind → Focus
  | .passive => .backtrack
  | .active => .rewrite

theorem OperationKind.finish_ne_search (k : OperationKind) : k.finish ≠ .search := by
  cases k <;> intro h <;> cases h

/-- Embed a primitive label at a fixed box-depth bound. -/
def primitiveLabel (ops : Operations Op) : (d : Nat) → Primitive Op → (alphabet ops d).Symbol
  | 0, p => ⟨p⟩
  | _ + 1, p => .inl p

theorem primitiveLabel_injective (d : Nat) {p q : Primitive Op}
    (h : primitiveLabel ops d p = primitiveLabel ops d q) : p = q := by
  cases d with
  | zero => exact congrArg ULift.down h
  | succ d => exact Sum.inl.inj h

/-- Certified decomposition of an actual operation's ordered incidence lists.
The argument prefix has the arity prescribed by the operation signature. -/
structure SearchOperation {d I O} (G : Hypernet ops d I O) where
  edge : G.Edge
  operation : Op
  label : G.edgeLabel edge = primitiveLabel ops d (.operation operation)
  source : G.Vertex
  arguments : List G.Vertex
  thunks : List G.Vertex
  source_eq : G.source edge = [source]
  target_eq : G.target edge = arguments ++ thunks
  arity : arguments.length = ops.arguments operation

namespace SearchOperation
variable {d I O} {G : Hypernet ops d I O}

/-- Every actual shallow operation edge admits a certified view; the decomposition
is derived from graph typing rather than assumed as a machine axiom. -/
theorem exists_view (e : G.Edge) (o : Op)
    (label : G.edgeLabel e = primitiveLabel ops d (.operation o)) :
    ∃ a : SearchOperation G, a.edge = e ∧ a.operation = o := by
  have src : (G.source e).length = 1 := by
    rw [G.source_length, label]
    cases d <;> rfl
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp src
  have len : ops.arguments o ≤ (G.target e).length := by
    rw [G.target_length, label]
    cases d <;> simp [primitiveLabel, alphabet, baseAlphabet, nextAlphabet, primitiveSignature]
  refine ⟨{
    edge := e, operation := o, label := label, source := v,
    arguments := (G.target e).take (ops.arguments o),
    thunks := (G.target e).drop (ops.arguments o),
    source_eq := hv, target_eq := (List.take_append_drop _ _).symm,
    arity := ?_ }, rfl, rfl⟩
  simp [List.length_take, Nat.min_eq_left len]

/-- Two views of the same edge have identical operational data. -/
theorem data_unique (a b : SearchOperation G) (eq : a.edge = b.edge) :
    a.operation = b.operation ∧ a.source = b.source ∧ a.arguments = b.arguments := by
  have labels := a.label.symm.trans ((congrArg G.edgeLabel eq).trans b.label)
  have op := Primitive.operation.inj (primitiveLabel_injective d labels)
  have src : [a.source] = [b.source] := a.source_eq.symm.trans ((congrArg G.source eq).trans b.source_eq)
  have targets : a.arguments ++ a.thunks = b.arguments ++ b.thunks :=
    a.target_eq.symm.trans ((congrArg G.target eq).trans b.target_eq)
  have len : a.arguments.length = b.arguments.length := a.arity.trans ((congrArg ops.arguments op).trans b.arity.symm)
  have args := congrArg (List.take a.arguments.length) targets
  simp only [List.take_left] at args
  rw [len, List.take_left] at args
  exact ⟨op, List.cons.inj src |>.1, args⟩

theorem argument_mem (a : SearchOperation G) {v} (h : v ∈ a.arguments) : v ∈ G.target a.edge := by
  rw [a.target_eq]
  exact List.mem_append_left _ h

theorem arguments_nodup (a : SearchOperation G) : a.arguments.Nodup := by
  have h := G.target_nodup a.edge
  rw [a.target_eq] at h
  exact (List.nodup_append.mp h).1

/-- The local result of search at the source of an operation (Fig. 9b,e). -/
def enter (kind : Op → OperationKind) (a : SearchOperation G) : Focus × G.Vertex :=
  match a.arguments with
  | [] => ((kind a.operation).finish, a.source)
  | v :: _ => (.search, v)

/-- Returning from argument i advances to i+1, or finishes (Fig. 9c,d). -/
def resume (kind : Op → OperationKind) (a : SearchOperation G) (i : Nat) : Focus × G.Vertex :=
  match a.arguments[i + 1]? with
  | some v => (.search, v)
  | none => ((kind a.operation).finish, a.source)

theorem enter_unique (kind : Op → OperationKind) (a b : SearchOperation G)
    (eq : a.edge = b.edge) : a.enter kind = b.enter kind := by
  obtain ⟨op, src, args⟩ := a.data_unique b eq
  simp only [enter, op, src, args]

theorem resume_unique (kind : Op → OperationKind) (a b : SearchOperation G)
    (eq : a.edge = b.edge) (i : Nat) : a.resume kind i = b.resume kind i := by
  obtain ⟨op, src, args⟩ := a.data_unique b eq
  simp only [resume, op, src, args]

/-- Retain an operation view when a different edge is filled. -/
noncomputable def plug (a : SearchOperation G) (hole : G.Edge) (ne : a.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (G.edgeLabel hole))
      ((alphabet ops d).signature.output (G.edgeLabel hole))) : SearchOperation (G.plug hole H) where
  edge := .inl ⟨a.edge, ne⟩
  operation := a.operation
  label := a.label
  source := Net.Replacement.host G hole H a.source
  arguments := a.arguments.map (Net.Replacement.host G hole H)
  thunks := a.thunks.map (Net.Replacement.host G hole H)
  source_eq := by change (G.source a.edge).map _ = [_]; rw [a.source_eq]; rfl
  target_eq := by change (G.target a.edge).map _ = _; rw [a.target_eq, List.map_append]
  arity := by simpa using a.arity

theorem plug_enter (kind : Op → OperationKind) (a : SearchOperation G)
    (hole : G.Edge) (ne : a.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (G.edgeLabel hole))
      ((alphabet ops d).signature.output (G.edgeLabel hole))) :
    (a.plug hole ne H).enter kind =
      (a.enter kind).map id (Net.Replacement.host G hole H) := by
  simp only [enter, plug]
  cases a.arguments <;> rfl

theorem plug_resume (kind : Op → OperationKind) (a : SearchOperation G)
    (hole : G.Edge) (ne : a.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (G.edgeLabel hole))
      ((alphabet ops d).signature.output (G.edgeLabel hole))) (i : Nat) :
    (a.plug hole ne H).resume kind i =
      (a.resume kind i).map id (Net.Replacement.host G hole H) := by
  simp only [resume, plug, List.getElem?_map]
  cases a.arguments[i + 1]? <;> rfl

end SearchOperation

/-- Token coordinates on the underlying graph; only outer vertices are used.
RealizedSearch relates these coordinates to erasure-based state search. -/
abbrev SearchPosition {d I O} (G : Hypernet ops d I O) := Focus × G.Vertex

/-- Fig. 9(a–e), with operation-entry and operation-return cases grouped.
No transition enters a box body or traverses a thunk target. -/
inductive SearchStep {d I O} (G : Hypernet ops d I O) (kind : Op → OperationKind) :
    SearchPosition G → SearchPosition G → Prop where
  | trigger (e : G.Edge) (v : G.Vertex)
      (label : G.edgeLabel e = primitiveLabel ops d .variable)
      (source : G.source e = [v]) : SearchStep G kind (.search, v) (.rewrite, v)
  | enter (a : SearchOperation G) : SearchStep G kind (.search, a.source) (a.enter kind)
  | resume (a : SearchOperation G) (i : Nat) (v : G.Vertex)
      (argument : a.arguments[i]? = some v) :
      SearchStep G kind (.backtrack, v) (a.resume kind i)

namespace SearchStep
variable {d I O} {G : Hypernet ops d I O} {kind : Op → OperationKind}

/-- Fig. 9b: inspect the first argument, skipping every thunk. -/
theorem first_argument (a : SearchOperation G) (v : G.Vertex) (rest : List G.Vertex)
    (args : a.arguments = v :: rest) :
    SearchStep G kind (.search, a.source) (.search, v) := by
  simpa [SearchOperation.enter, args] using SearchStep.enter (kind := kind) a

/-- Fig. 9e: a nullary operation immediately finishes in its declared mode. -/
theorem nullary (a : SearchOperation G) (args : a.arguments = []) :
    SearchStep G kind (.search, a.source) ((kind a.operation).finish, a.source) := by
  simpa [SearchOperation.enter, args] using SearchStep.enter (kind := kind) a

/-- Fig. 9c: returning from an argument searches the next argument. -/
theorem next_argument (a : SearchOperation G) (i : Nat) (v w : G.Vertex)
    (arg : a.arguments[i]? = some v) (next : a.arguments[i + 1]? = some w) :
    SearchStep G kind (.backtrack, v) (.search, w) := by
  simpa [SearchOperation.resume, next] using SearchStep.resume (kind := kind) a i v arg

/-- Fig. 9d: returning from the last argument finishes the operation. -/
theorem last_argument (a : SearchOperation G) (i : Nat) (v : G.Vertex)
    (arg : a.arguments[i]? = some v) (last : a.arguments[i + 1]? = none) :
    SearchStep G kind (.backtrack, v) ((kind a.operation).finish, a.source) := by
  simpa [SearchOperation.resume, last] using SearchStep.resume (kind := kind) a i v arg

/-- Equal input coordinates force equal results, independently of rule witnesses. -/
theorem result_unique {s s' t u : SearchPosition G}
    (left : SearchStep G kind s t) (right : SearchStep G kind s' u) (same : s = s') : t = u := by
  cases left with
  | trigger e v label source =>
      cases right with
      | trigger f w label' source' => exact congrArg (fun x => (Focus.rewrite, x)) (Prod.mk.inj same).2
      | enter a =>
          have vs := (Prod.mk.inj same).2
          have eq : e = a.edge := G.source_unique (v := v) (by simp [source]) (by simp [a.source_eq, vs])
          have bad := primitiveLabel_injective d (label.symm.trans ((congrArg G.edgeLabel eq).trans a.label))
          cases bad
      | resume a i w arg => cases (Prod.mk.inj same).1
  | enter a =>
      cases right with
      | trigger e v label source =>
          have vs := (Prod.mk.inj same).2
          have eq : a.edge = e := G.source_unique (v := v) (by simp [a.source_eq, vs]) (by simp [source])
          have bad := primitiveLabel_injective d (a.label.symm.trans ((congrArg G.edgeLabel eq).trans label))
          cases bad
      | enter b =>
          have vs := (Prod.mk.inj same).2
          apply a.enter_unique kind b
          exact G.source_unique (v := a.source) (by simp [a.source_eq]) (by simp [b.source_eq, vs])
      | resume b i w arg => cases (Prod.mk.inj same).1
  | resume a i v argument =>
      cases right with
      | trigger e w label source => cases (Prod.mk.inj same).1
      | enter b => cases (Prod.mk.inj same).1
      | resume b j w argument' =>
          have vw := (Prod.mk.inj same).2
          subst w
          have am : v ∈ a.arguments := List.mem_of_getElem? argument
          have bm : v ∈ b.arguments := List.mem_of_getElem? argument'
          have eq := G.target_unique (a.argument_mem am) (b.argument_mem bm)
          have args := (a.data_unique b eq).2.2
          have ij : i = j := by
            rw [← args] at argument'
            exact a.arguments_nodup.eq_of_getElem?_eq
              (List.getElem?_eq_some_iff.mp argument).1 (argument.trans argument'.symm)
          subst j
          exact a.resume_unique kind b eq i

/-- Search determinism follows from incidence uniqueness and ordered arguments. -/
theorem deterministic {s t u : SearchPosition G}
    (left : SearchStep G kind s t) (right : SearchStep G kind s u) : t = u :=
  result_unique left right rfl

/-- A triggering token cannot make a search transition. -/
theorem no_rewrite {v : G.Vertex} {t} : ¬ SearchStep G kind (.rewrite, v) t := by
  intro h
  cases h

/-- Backtracking at an input is search-normal: no edge can target an input. -/
theorem final_no_step {v : G.Vertex} (input : v.IsInput) {t} :
    ¬ SearchStep G kind (.backtrack, v) t := by
  intro h
  cases h with
  | resume a i _ arg => exact G.target_not_input (a.argument_mem (List.mem_of_getElem? arg)) input

/-- Any search-mode target lies on an operation target, hence is not an input. -/
theorem search_target_not_input {s t : SearchPosition G} (step : SearchStep G kind s t)
    (search : t.1 = .search) : ¬ t.2.IsInput := by
  cases step with
  | trigger e v label source => cases search
  | enter a =>
      simp only [SearchOperation.enter] at search ⊢
      split at *
      next empty => exact False.elim ((kind a.operation).finish_ne_search search)
      next x xs args => exact G.target_not_input (a.argument_mem (by simp [args]))
  | resume a i w arg =>
      simp only [SearchOperation.resume] at search ⊢
      split at *
      next x nextArg => exact G.target_not_input (a.argument_mem (List.mem_of_getElem? nextArg))
      next none => exact False.elim ((kind a.operation).finish_ne_search search)

/-- No search step produces a searching token at an input (§6.4). -/
theorem no_initial_target {s : SearchPosition G} {v : G.Vertex} (input : v.IsInput) :
    ¬ SearchStep G kind s (.search, v) :=
  fun step => search_target_not_input step rfl input

/-- An existing context search step survives every filling of a shallow hole.
The hole is neither an operation nor a variable, so the interacting edge survives. -/
theorem plug {s t : SearchPosition G} (step : SearchStep G kind s t)
    (hole : G.Edge) (h : Hole) (label : G.edgeLabel hole = primitiveLabel ops d (.hole h))
    (H : Hypernet ops d ((alphabet ops d).signature.input (G.edgeLabel hole))
      ((alphabet ops d).signature.output (G.edgeLabel hole))) :
    SearchStep (G.plug hole H) kind
      (s.map id (Net.Replacement.host G hole H))
      (t.map id (Net.Replacement.host G hole H)) := by
  cases step with
  | trigger e v el src =>
      have ne : e ≠ hole := by
        intro eq
        have bad := primitiveLabel_injective d (el.symm.trans ((congrArg G.edgeLabel eq).trans label))
        cases bad
      apply SearchStep.trigger (G := G.plug hole H) (.inl ⟨e, ne⟩) _ el
      change (G.source e).map _ = [_]
      rw [src]
      rfl
  | enter a =>
      have ne : a.edge ≠ hole := by
        intro eq
        have bad := primitiveLabel_injective d (a.label.symm.trans ((congrArg G.edgeLabel eq).trans label))
        cases bad
      have result := SearchStep.enter (kind := kind) (a.plug hole ne H)
      rw [a.plug_enter kind hole ne H] at result
      exact result
  | resume a i v arg =>
      have ne : a.edge ≠ hole := by
        intro eq
        have bad := primitiveLabel_injective d (a.label.symm.trans ((congrArg G.edgeLabel eq).trans label))
        cases bad
      have mapped : (a.plug hole ne H).arguments[i]? = some (Net.Replacement.host G hole H v) := by
        simp only [SearchOperation.plug, List.getElem?_map, arg, Option.map_some]
      have result := SearchStep.resume (kind := kind) (a.plug hole ne H) i _ mapped
      rw [a.plug_resume kind hole ne H i] at result
      exact result

end SearchStep
end Hypernets.Linear
