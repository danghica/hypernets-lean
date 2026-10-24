import Hypernets.Graph.StateQuotient
import Hypernets.Graph.ErasureExamples

/-! Concrete execution, reconstructed source names, and quotient determinism. -/
namespace Hypernets.Linear.Examples
open Graph

/-- The coordinate value step reaches the specific previously constructed final state. -/
theorem value_search_final : State.Search (fun _ => .passive) initialValue finalValue :=
  TypedPosition.search_realize (TypedPosition.initial value)
    ((TypedPosition.initial value).advance SearchExamples.value_finishes)
    value_focusFree value_holeFree SearchExamples.value_finishes

/-- A reconstructed value state has different carriers, but represents the same state. -/
noncomputable def recoveredValue : State operations 0 :=
  (State.coordinate initialValue).realize initialValue.focussed.underlying_focusFree
    (initialValue.focussed.underlying_holeFree initialValue.hole_free)

theorem recovered_value_search : State.Search (fun _ => .passive) recoveredValue finalValue :=
  State.search_source_iso value_search_final (State.recover initialValue).symm

theorem recovered_value_class : StateClass.ofState recoveredValue = StateClass.ofState initialValue :=
  Quotient.sound ⟨State.recover initialValue⟩

/-- Every class-level successor of the value is exactly its final-state class. -/
theorem value_class_successor (t : StateClass operations 0)
    (step : StateClass.Search (fun _ => .passive) (StateClass.ofState initialValue) t) :
    t = StateClass.ofState finalValue :=
  StateClass.search_deterministic step value_search_final

end Hypernets.Linear.Examples
