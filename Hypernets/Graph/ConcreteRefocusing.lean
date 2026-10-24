import Hypernets.Graph.RootedPathObstruction

/-! The paper's refocusing predicate on concrete recursive state classes.
Search satisfies it; preservation by rewriting remains a separate obligation. -/
namespace Hypernets.Linear.DeepStateClass
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

/-- Rootedness is exactly search reachability from an initial state. Preservation
of the erased graph ensures this initial class is the correct canonical root. -/
theorem rooted_iff_initial_run (s : DeepStateClass ops d) :
    Rooted kind s ↔ ∃ initial n, Initial initial ∧ (searchMachine kind).Steps n initial s := by
  constructor
  · rintro ⟨n, run⟩
    exact ⟨root s, n, root_initial s, run⟩
  · rintro ⟨initial, n, hi, run⟩
    have eq : initial = root s := (root_eq_of_initial hi).symm.trans (steps_root run)
    exact ⟨n, eq ▸ run⟩

/-- A transition relation is refocusing when every transition preserves the
concrete rooted predicate defined from search on the state's own underlying graph. -/
def Refocusing (kind : Op → OperationKind)
    (transition : DeepStateClass ops d → DeepStateClass ops d → Prop) : Prop :=
  ∀ {s t}, Rooted kind s → transition s t → Rooted kind t

/-- The intrinsic search component is refocusing without assumptions on extrinsic behavior. -/
theorem search_refocusing : Refocusing (ops := ops) (d := d) kind (Search kind) := by
  intro s t rooted step
  exact rooted_search rooted step

/-- Adding search leaves precisely the rootedness obligation for the supplied
rewrite relation. This does not assert that arbitrary rewrites satisfy it. -/
theorem refocusing_with_search (rewrite : DeepStateClass ops d → DeepStateClass ops d → Prop) :
    Refocusing kind (fun s t => Search kind s t ∨ rewrite s t) ↔ Refocusing kind rewrite := by
  constructor
  · intro ref s t rooted step
    exact ref rooted (Or.inr step)
  · intro ref s t rooted step
    cases step with
    | inl search => exact rooted_search rooted search
    | inr rewrite => exact ref rooted rewrite

/-- In any concrete transition machine satisfying refocusing, every execution
from an initial state stays rooted, regardless of how often it rewrites. -/
theorem refocusing_execution {M : Machine (DeepStateClass ops d)}
    (ref : Refocusing kind M.step) {n} {s t : DeepStateClass ops d}
    (initial : Initial s) (run : M.Steps n s t) : Rooted kind t := by
  have invariant : ∀ {x y : DeepStateClass ops d} {m},
      M.Steps m x y → Rooted kind x → Rooted kind y := by
    intro x y m run
    induction run with
    | zero => exact id
    | cons step _ ih => exact fun rooted => ih (ref rooted step)
  exact invariant run (initial_rooted initial)

end Hypernets.Linear.DeepStateClass
