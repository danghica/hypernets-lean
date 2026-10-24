import Hypernets.Graph.DeepStateQuotient

/-! The literal-label quotient maps onto the recursively renamed quotient,
preserving and lifting search transitions. -/
namespace Hypernets.Linear.StateClass
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- Forget the choice of literal box-body representatives. -/
def toDeep (s : StateClass ops d) : DeepStateClass ops d :=
  Quotient.liftOn s (fun s => DeepStateClass.ofState s)
    (fun _ _ ⟨a⟩ => Quotient.sound ⟨Focussed.DeepIso.ofIso a⟩)

theorem toDeep_ofState (s : State ops d) :
    toDeep (ofState s) = DeepStateClass.ofState s := rfl

/-- Every recursive state class has a literal-label class above it. -/
theorem toDeep_surjective (s : DeepStateClass ops d) : ∃ t, toDeep t = s := by
  induction s using Quotient.inductionOn with
  | h s => exact ⟨ofState s, rfl⟩

/-- Literal-label search projects to recursive search. -/
theorem search_toDeep {kind : Op → OperationKind} {s t : StateClass ops d}
    (step : Search kind s t) : DeepStateClass.Search kind (toDeep s) (toDeep t) := by
  induction s, t using Quotient.inductionOn₂ with
  | h s t => exact State.search_deepSearch step

/-- Every recursive step lifts from any specified literal source representative.
Only the target representative may need to be changed. -/
theorem search_lift {kind : Op → OperationKind} (s : StateClass ops d)
    (t : DeepStateClass ops d) (step : DeepStateClass.Search kind (toDeep s) t) :
    ∃ u : StateClass ops d, Search kind s u ∧ toDeep u = t := by
  induction s, t using Quotient.inductionOn₂ with
  | h s t =>
      obtain ⟨u, su, ⟨ut⟩⟩ := State.deepSearch_iff.mp step
      exact ⟨ofState u, su, Quotient.sound ⟨ut⟩⟩

/-- The recursive quotient has exactly the projected literal search steps. -/
theorem search_toDeep_iff {kind : Op → OperationKind} (s : StateClass ops d)
    (t : DeepStateClass ops d) :
    DeepStateClass.Search kind (toDeep s) t ↔
      ∃ u, Search kind s u ∧ toDeep u = t := by
  constructor
  · exact search_lift s t
  · rintro ⟨u, step, rfl⟩
    exact search_toDeep step

theorem initial_toDeep (s : StateClass ops d) : DeepStateClass.Initial (toDeep s) ↔ Initial s := by
  induction s using Quotient.inductionOn with
  | h s => exact Iff.rfl

theorem final_toDeep (s : StateClass ops d) : DeepStateClass.Final (toDeep s) ↔ Final s := by
  induction s using Quotient.inductionOn with
  | h s => exact Iff.rfl

/-- Quotienting recursive box names preserves and reflects search normal forms. -/
theorem no_search_toDeep {kind : Op → OperationKind} (s : StateClass ops d) :
    (¬ ∃ t, DeepStateClass.Search kind (toDeep s) t) ↔ ¬ ∃ u, Search kind s u := by
  constructor
  · rintro no ⟨u, step⟩
    exact no ⟨toDeep u, search_toDeep step⟩
  · rintro no ⟨t, step⟩
    obtain ⟨u, su, _⟩ := search_lift s t step
    exact no ⟨u, su⟩

end Hypernets.Linear.StateClass
