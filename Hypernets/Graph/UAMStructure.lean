import Hypernets.Graph.SubstitutionDeterminism

/-! The full linear UAM's determinism and refocusing theorem, paper Lemma 3. -/
namespace Hypernets.Linear
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

/-- Determinism of named states means uniqueness up to recursive graph isomorphism. -/
def DeterministicModulo (R : State ops d → State ops d → Prop) : Prop :=
  ∀ {s t u}, R s t → R s u → Nonempty (Focussed.DeepIso t.focussed u.focussed)

/-- Refocusing for actual states uses the rooted predicate on recursive classes. -/
def RefocusingStates (kind : Op → OperationKind) (R : State ops d → State ops d → Prop) : Prop :=
  ∀ {s t}, State.Rooted kind s → R s t → State.Rooted kind t

namespace UAM
variable (B : Behaviour ops d kind)

/-- Intrinsic steps preserve rootedness, including concrete substitution. -/
theorem intrinsic_refocusing : RefocusingStates (ops := ops) (d := d) kind (Intrinsic kind) := by
  intro s t root step
  rcases step with search | sub
  · exact DeepStateClass.rooted_search root (State.search_deepSearch search)
  · exact State.substitution_rooted sub root

/-- Determinism of the behaviour gives determinism of the complete UAM.
The proof uses proved substitution uniqueness and source exclusivity. -/
theorem deterministic (behaviour : DeterministicModulo B.step) : DeterministicModulo (Step B) := by
  intro s t u left right
  rcases (step_iff B).mp left with search | sub | ext
  · rcases (step_iff B).mp right with search' | rewrite
    · exact State.deepSearch_deterministic (State.search_deepSearch search) (State.search_deepSearch search')
    · exact False.elim (search_rewrite_exclusive B search rewrite)
  · rcases (step_iff B).mp right with search | sub' | ext
    · exact False.elim (search_rewrite_exclusive B search (.inl sub))
    · exact State.substitution_deterministic sub sub'
    · exact False.elim (State.substitution_not_compute sub (B.compute ext))
  · rcases (step_iff B).mp right with search | sub | ext'
    · exact False.elim (search_rewrite_exclusive B search (.inr ext))
    · exact False.elim (State.substitution_not_compute sub (B.compute ext))
    · exact behaviour ext ext'

/-- Full-UAM determinism is equivalent to determinism of its extrinsic behaviour. -/
theorem deterministic_iff : DeterministicModulo (Step B) ↔ DeterministicModulo B.step := by
  constructor
  · intro full s t u left right
    exact full (.inr left) (.inr right)
  · exact deterministic B

/-- Refocusing of the behaviour extends to the complete UAM. -/
theorem refocusing (behaviour : RefocusingStates kind B.step) : RefocusingStates kind (Step B) := by
  intro s t root step
  rcases step with intrinsic | ext
  · exact intrinsic_refocusing root intrinsic
  · exact behaviour root ext

/-- Refocusing has precisely the remaining extrinsic rootedness requirement. -/
theorem refocusing_iff : RefocusingStates kind (Step B) ↔ RefocusingStates kind B.step := by
  constructor
  · intro full s t root ext
    exact full root (.inr ext)
  · exact refocusing B

/-- Every full execution preserves rootedness, however often it rewrites. -/
theorem rooted_execution (behaviour : RefocusingStates kind B.step)
    {n s t} (run : (machine B).Steps n s t) (root : State.Rooted kind s) : State.Rooted kind t := by
  induction run with
  | zero => exact root
  | cons step _ ih => exact ih (refocusing B behaviour root step)

/-- In particular all states reached from initial attachment are rooted. -/
theorem initial_execution_rooted (behaviour : RefocusingStates kind B.step)
    {n s t} (run : (machine B).Steps n s t) (initial : s.focussed.Initial) : State.Rooted kind t :=
  rooted_execution B behaviour run (DeepStateClass.initial_rooted initial)

/-- The empty-behaviour UAM has both structural properties without hypotheses. -/
theorem empty_structural (ops : Operations Op) (d : Nat) (kind : Op → OperationKind) :
    DeterministicModulo (Step (emptyBehaviour ops d kind)) ∧
      RefocusingStates kind (Step (emptyBehaviour ops d kind)) :=
  ⟨deterministic _ (fun h => False.elim h),refocusing _ (fun _ h => False.elim h)⟩
end UAM
end Hypernets.Linear
