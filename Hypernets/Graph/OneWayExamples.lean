import Hypernets.Graph.OneWayObstruction
import Hypernets.Graph.RootedExamples

/-! Positive and negative one-way examples, including the term-output restriction. -/
namespace Hypernets.Linear.Examples
open Graph

/-- A variable wire is one-way despite having a term input-to-output path. -/
theorem variable_oneWay : OneWay variableFragment := by
  apply oneWay_iff.mpr
  intro j _ root
  have target : Port.output j ∈ variableFragment.target 0 := by
    have eq : j = 0 := Fin.ext (by change j.val = 0; have h : j.val < 1 := j.isLt; omega)
    subst j
    decide
  have bad := root.incoming_operation target
  exact bad

/-- The existing operation corolla is not one-way: its first term argument
is reached by its sole operation edge. -/
theorem operation_not_oneWay : ¬ OneWay SearchExamples.graph := by
  intro one
  apply (oneWay_iff.mp one) 0 rfl
  exact ⟨0, [0], .cons (by trivial) (by decide) (by decide) (.nil _)⟩

/-- An operation exposing only a thunk, with no term arguments. -/
@[reducible] def thunkOnlyOperations : Operations Unit := ⟨fun _ => 0, fun _ => [0]⟩

@[reducible] def thunkOnlyGraph : Hypernet thunkOnlyOperations 0 [.term] [.thunk 0] :=
  Net.corolla (alphabet thunkOnlyOperations 0).signature
    (primitiveLabel thunkOnlyOperations 0 (.operation ()))

/-- One-wayness deliberately permits operation paths ending at thunk outputs. -/
theorem thunk_only_oneWay : OneWay thunkOnlyGraph := by
  apply oneWay_iff.mpr
  intro j term
  have eq : j = 0 := Fin.ext (by change j.val = 0; have h : j.val < 1 := j.isLt; omega)
  subst j
  cases term

/-- A checked witness that one-wayness does not forbid every output path. -/
theorem thunk_output_reachable : OperationReachable thunkOnlyGraph (.output 0) :=
  ⟨0, [0], .cons (by trivial) (by decide) (by decide) (.nil _)⟩

/-- Replace the variable preceding the interior focus by a genuine hole.
The focus remains internal, after the hole and before the value edge. -/
@[reducible] noncomputable def oneWayContext : Hypernet operations 0 [.term] [] :=
  interiorState.graph.relabelEdges (alphabet operations 0).signature
    (fun e => match e with
      | .inl (.inl _) => primitiveLabel operations 0 (.operation Op.value)
      | .inl (.inr _) => primitiveLabel operations 0 (.hole (chainHole 0))
      | .inr _ => focusLabel operations 0 .search)
    (by intro e; cases e with
        | inl e => cases e <;> rfl
        | inr e => rfl)
    (by intro e; cases e with
        | inl e => cases e <;> rfl
        | inr e => rfl)

/-- The surviving focus of the single-hole context. -/
noncomputable def oneWayContext_focus : Focussed oneWayContext where
  edge := .inr 0
  mode := .search
  label := rfl
  source := interiorState.focussed.source
  target := interiorState.focussed.target
  source_eq := interiorState.focussed.source_eq
  target_eq := interiorState.focussed.target_eq
  self_acyclic := interiorState.focussed.self_acyclic
  not_exposed := interiorState.focussed.not_exposed
  other_free := by
    intro e ne
    cases e with
    | inl e => cases e <;> intro m bad <;> cases bad
    | inr e =>
        have eq : e = 0 := Fin.ext (by have h : e.val < 1 := e.isLt; omega)
        exact False.elim (ne (congrArg Sum.inr eq))

/-- Filling the only hole by a variable leaves no holes at any depth. -/
theorem oneWayContext_filled_closed :
    HoleFree (oneWayContext.plug (.inl (.inr 0)) variableFragment) := by
  intro h present
  cases (plug_hasHole_iff oneWayContext (.inl (.inr 0)) variableFragment h).mp present with
  | inr inside => exact variableFragment_holeFree h inside
  | inl retained =>
      obtain ⟨e, ne, x, label⟩ := retained
      cases e with
      | inr e => cases x with
        | inl u => cases label
        | inr child => exact Empty.elim child
      | inl e => cases e with
        | inl e => cases x with
          | inl u => cases label
          | inr child => exact Empty.elim child
        | inr e =>
            have eq : e = 0 := Fin.ext (by have h : e.val < 1 := e.isLt; omega)
            exact ne (congrArg Sum.inl (congrArg Sum.inr eq))

/-- Lemma 26(2) applies to a genuine filled state whose offending context path
is precisely the hole edge, so the path does not survive as a retained edge. -/
theorem oneWay_filled_not_rooted (kind : Op → OperationKind) :
    ¬ State.Rooted kind (oneWayContext_focus.filledState (.inl (.inr 0))
      (by intro h; cases h) variableFragment variableFragment_focusFree oneWayContext_filled_closed) := by
  apply Focussed.oneWay_not_rooted oneWayContext_focus (.inl (.inr 0))
    (by intro h; cases h) variableFragment variableFragment_focusFree oneWayContext_filled_closed variable_oneWay
    (Net.Path.single (G := oneWayContext) (.inl (.inr 0))) rfl
  · exact List.mem_map.mpr ⟨.internal (.inr 0), List.mem_singleton_self _, rfl⟩
  · exact List.mem_singleton_self _
  · exact id

end Hypernets.Linear.Examples
