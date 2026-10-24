import Hypernets.Graph.DeepStateSearch

/-! Search and boundary observations on focus-preserving isomorphism classes.
The isomorphism allows independent renaming in every nested box body. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type}

/-- Equivalence of states by a focus-preserving recursive-label isomorphism. -/
def deepStateSetoid (ops : Operations Op) (d : Nat) : Setoid (State ops d) where
  r s t := Nonempty (Focussed.DeepIso s.focussed t.focussed)
  iseqv := ⟨fun _ => ⟨Focussed.DeepIso.refl _⟩,
    fun ⟨a⟩ => ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b⟩⟩

/-- Named state representatives identified by focus-preserving isomorphism. -/
abbrev DeepStateClass (ops : Operations Op) (d : Nat) := Quotient (deepStateSetoid ops d)

namespace DeepStateClass
variable {ops : Operations Op} {d : Nat}

/-- The isomorphism class of a concrete state. -/
def ofState (s : State ops d) : DeepStateClass ops d := Quotient.mk _ s

/-- Descend the actual relation; independence of both representatives is proved. -/
def Search (kind : Op → OperationKind) (s t : DeepStateClass ops d) : Prop :=
  Quotient.liftOn₂ s t (State.DeepSearch kind)
    (fun _ _ _ _ ⟨a⟩ ⟨b⟩ => propext (State.deepSearch_iso_iff a b))

theorem search_iff (kind : Op → OperationKind) (s t : State ops d) :
    Search kind (ofState s) (ofState t) ↔ State.DeepSearch kind s t := Iff.rfl

/-- Determinism becomes equality of successor classes. -/
theorem search_deterministic {kind : Op → OperationKind} {s t u : DeepStateClass ops d}
    (left : Search kind s t) (right : Search kind s u) : t = u := by
  induction s, t, u using Quotient.inductionOn₃ with
  | h s t u => exact Quotient.sound (State.deepSearch_deterministic left right)

/-- Initiality is independent of the chosen state representative. -/
def Initial (s : DeepStateClass ops d) : Prop :=
  Quotient.liftOn s (fun s => s.focussed.Initial)
    (fun _ _ ⟨a⟩ => propext a.initial_iff)

/-- Finality is independent of the chosen state representative. -/
def Final (s : DeepStateClass ops d) : Prop :=
  Quotient.liftOn s (fun s => s.focussed.Final)
    (fun _ _ ⟨a⟩ => propext a.final_iff)

theorem initial_iff (s : State ops d) : Initial (ofState s) ↔ s.focussed.Initial := Iff.rfl

theorem final_iff (s : State ops d) : Final (ofState s) ↔ s.focussed.Final := Iff.rfl

/-- Final classes have no search successor. This concerns search alone. -/
theorem final_no_search {kind : Op → OperationKind} {s t : DeepStateClass ops d}
    (final : Final s) : ¬ Search kind s t := by
  induction s, t using Quotient.inductionOn₂ with
  | h s t => exact State.final_no_deepSearch final

/-- No search transition reaches an initial class. -/
theorem no_search_initial {kind : Op → OperationKind} {s t : DeepStateClass ops d}
    (initial : Initial t) : ¬ Search kind s t := by
  induction s, t using Quotient.inductionOn₂ with
  | h s t => exact State.no_deepSearch_initial initial

end DeepStateClass
end Hypernets.Linear
