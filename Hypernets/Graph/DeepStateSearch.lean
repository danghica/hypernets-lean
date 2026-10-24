import Hypernets.Graph.DeepErasureRenaming

/-! Search allowing independent renaming inside all nested boxes at its endpoint. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}
namespace State

/-- Erasure-based search on actual states. Targets may use arbitrary vertex and
edge names, provided they are recursively focus-preservingly isomorphic to the realized result.
HoleContextSearch proves equivalence to contextual finite-pattern rewriting. -/
def DeepSearch (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  ∃ q : TypedPosition s.focussed.underlying,
    SearchStep s.focussed.underlying kind (coordinate s).val q.val ∧
    Nonempty (Focussed.DeepIso (q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)).focussed t.focussed)

/-- Every coordinate successor yields an actual state successor. -/
theorem deepSearch_realize (kind : Op → OperationKind) (s : State ops d)
    (q : TypedPosition s.focussed.underlying)
    (step : SearchStep s.focussed.underlying kind (coordinate s).val q.val) :
    DeepSearch kind s (q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free)) :=
  ⟨q, step, ⟨Focussed.DeepIso.refl _⟩⟩

/-- Renaming a successor while preserving its focus preserves the search step. -/
theorem deepSearch_target_iso {kind : Op → OperationKind} {s t u : State ops d}
    (step : DeepSearch kind s t) (iso : Focussed.DeepIso t.focussed u.focussed) : DeepSearch kind s u := by
  obtain ⟨q, hq, ⟨qt⟩⟩ := step
  exact ⟨q, hq, ⟨qt.trans iso⟩⟩

/-- DeepSearch is deterministic modulo focus-preserving graph isomorphism. -/
theorem deepSearch_deterministic {kind : Op → OperationKind} {s t u : State ops d}
    (left : DeepSearch kind s t) (right : DeepSearch kind s u) : Nonempty (Focussed.DeepIso t.focussed u.focussed) := by
  obtain ⟨q, hq, ⟨qt⟩⟩ := left
  obtain ⟨r, hr, ⟨ru⟩⟩ := right
  have eq : q = r := Subtype.ext (SearchStep.deterministic hq hr)
  subst r
  exact ⟨qt.symm.trans ru⟩

/-- An explicit final state has no erasure-based search transition. -/
theorem final_no_deepSearch {kind : Op → OperationKind} {s t : State ops d}
    (final : s.focussed.Final) : ¬ DeepSearch kind s t := by
  rintro ⟨q, step, _⟩
  have b := (coordinate_boundary s).2.mpr final
  have eq : (coordinate s).val = (.backtrack, (coordinate s).val.2) := Prod.ext b.1 rfl
  rw [eq] at step
  exact SearchStep.final_no_step b.2 step

/-- No erasure-based search transition ends in an explicit initial state. -/
theorem no_deepSearch_initial {kind : Op → OperationKind} {s t : State ops d}
    (initial : t.focussed.Initial) : ¬ DeepSearch kind s t := by
  rintro ⟨q, step, ⟨iso⟩⟩
  have h := iso.initial_iff.mpr initial
  have b := (q.realize_boundary s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free)).1.mp h
  have eq : q.val = (.search, q.val.2) := Prod.ext b.1 rfl
  rw [eq] at step
  exact SearchStep.no_initial_target b.2 step

/-- Extracted coordinates agree under the erased isomorphism. -/
theorem coordinate_deepIso (a : Focussed.DeepIso s.focussed t.focussed) :
    (coordinate s).deepRename a.erased = coordinate t := by
  apply Subtype.ext
  apply Prod.ext
  · exact a.mode
  · exact a.erased_position

/-- Renaming a source state preserves the erasure-based search relation. -/
theorem deepSearch_source_iso {kind : Op → OperationKind} {u : State ops d}
    (step : DeepSearch kind s u) (a : Focussed.DeepIso s.focussed t.focussed) : DeepSearch kind t u := by
  obtain ⟨q, step, ⟨qu⟩⟩ := step
  have mapped := step.deepRename a.erased
  change SearchStep t.focussed.underlying kind ((coordinate s).deepRename a.erased).val
    (q.deepRename a.erased).val at mapped
  rw [coordinate_deepIso a] at mapped
  refine ⟨q.deepRename a.erased, mapped, ⟨?_⟩⟩
  exact (q.realize_deepRename a.erased s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free) t.focussed.underlying_focusFree
    (t.focussed.underlying_holeFree t.hole_free)).symm.trans qu

/-- The relation is invariant in both arguments, so it can descend to classes. -/
theorem deepSearch_iso_iff {kind : Op → OperationKind} {u v : State ops d}
    (a : Focussed.DeepIso s.focussed t.focussed) (b : Focussed.DeepIso u.focussed v.focussed) :
    DeepSearch kind s u ↔ DeepSearch kind t v := by
  constructor
  · intro step
    exact deepSearch_target_iso (deepSearch_source_iso step a) b
  · intro step
    exact deepSearch_target_iso (deepSearch_source_iso step a.symm) b.symm

/-- Literal-label state search embeds in recursively renamed search. -/
theorem search_deepSearch {kind : Op → OperationKind} {s t : State ops d}
    (step : Search kind s t) : DeepSearch kind s t := by
  obtain ⟨q, hq, ⟨qt⟩⟩ := step
  exact ⟨q, hq, ⟨Focussed.DeepIso.ofIso qt⟩⟩

/-- Recursive search adds exactly recursive endpoint renaming, not new local rules. -/
theorem deepSearch_iff {kind : Op → OperationKind} {s t : State ops d} :
    DeepSearch kind s t ↔ ∃ u, Search kind s u ∧ Nonempty (Focussed.DeepIso u.focussed t.focussed) := by
  constructor
  · rintro ⟨q, step, iso⟩
    exact ⟨q.realize s.focussed.underlying_focusFree
      (s.focussed.underlying_holeFree s.hole_free), search_realize kind s q step, iso⟩
  · rintro ⟨u, step, ⟨iso⟩⟩
    exact deepSearch_target_iso (search_deepSearch step) iso

end State
end Hypernets.Linear
