import Hypernets.Graph.Paths
import Hypernets.Transition

/-!
Concrete operation-path uniqueness, the graph-theoretic content of Lemma 22.
Only the defining single-source property of operation edges is assumed.
Determinism of reverse traversal is proved from unique target incidence.
-/

namespace Hypernets.Graph.Net

universe u

variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (G : Net σ I O) (operation : Op → Prop)

def UnaryOperations : Prop :=
  ∀ e, operation (G.edgeLabel e) → (G.source e).length = 1

def OperationStep (s t : G.Vertex) : Prop :=
  ∃ e, operation (G.edgeLabel e) ∧ s ∈ G.source e ∧ t ∈ G.target e

/-- Reverse operation traversal, with inputs as successful normal forms. -/
def reverseOperations : Machine G.Vertex where
  step s t := G.OperationStep operation t s
  final := Port.IsInput
  final_normal := by
    rintro s t hs ⟨e, _, _, target⟩
    exact G.target_not_input target hs

theorem reverseOperations_deterministic (unary : G.UnaryOperations operation) :
    (G.reverseOperations operation).Deterministic := by
  rintro v a b ⟨e, he, ha, hv⟩ ⟨f, hf, hb, hv'⟩
  have eq := G.target_unique hv hv'
  subst f
  have size := unary e he
  cases src : G.source e with
  | nil => simp [src] at ha
  | cons w ws =>
      have empty : ws = [] := by simpa [src] using size
      subst ws
      have aw : a = w := by simpa [src] using ha
      have bw : b = w := by simpa [src] using hb
      exact aw.trans bw.symm

/-- A reverse traversal records actual edges, not just its number of steps. -/
inductive OperationTrace (G : Net σ I O) (operation : Op → Prop) :
    G.Vertex → List G.Edge → G.Vertex → Prop where
  | nil (v) : OperationTrace G operation v [] v
  | cons {v w z e es} : operation (G.edgeLabel e) →
      v ∈ G.target e → w ∈ G.source e →
      OperationTrace G operation w es z → OperationTrace G operation v (e :: es) z

theorem OperationTrace.steps {s t es} (h : G.OperationTrace operation s es t) :
    (G.reverseOperations operation).Steps es.length s t := by
  induction h with
  | nil v => exact .zero _
  | cons he target source _ ih => exact .cons ⟨_, he, source, target⟩ ih

/-- This is exact uniqueness of the edge sequence, including its starting input.
It is stronger than merely asserting uniqueness of the execution length. -/
theorem OperationTrace.unique_to_inputs (unary : G.UnaryOperations operation)
    {v a b : G.Vertex} {es fs : List G.Edge}
    (h : G.OperationTrace operation v es a)
    (h' : G.OperationTrace operation v fs b)
    (ha : a.IsInput) (hb : b.IsInput) : es = fs ∧ a = b := by
  induction h generalizing fs b with
  | nil =>
      cases h' with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ target _ _ => exact False.elim (G.target_not_input target ha)
  | @cons v w z e es he target source tail ih =>
      cases h' with
      | nil => exact False.elim (G.target_not_input target hb)
      | @cons _ w' _ f fs hf target' source' tail' =>
          have ef := G.target_unique target target'
          subst f
          have ww : w = w' :=
            G.reverseOperations_deterministic operation unary
              ⟨e, he, source, target⟩ ⟨e, hf, source', target'⟩
          subst w'
          obtain ⟨edges, inputs⟩ := ih tail' ha hb
          exact ⟨congrArg (e :: ·) edges, inputs⟩

/-- Forward operation paths are recorded in forward edge order. -/
def OperationPath (s : G.Vertex) (es : List G.Edge) (t : G.Vertex) : Prop :=
  G.OperationTrace operation t es.reverse s

theorem operationPath_unique_from_inputs (unary : G.UnaryOperations operation)
    {v : G.Vertex} {es fs : List G.Edge} {i j : Fin I.length}
    (h : G.OperationPath operation (.input i) es v)
    (h' : G.OperationPath operation (.input j) fs v) : es = fs ∧ i = j := by
  obtain ⟨edges, inputs⟩ := OperationTrace.unique_to_inputs G operation unary h h' trivial trivial
  exact ⟨List.reverse_inj.mp edges, Port.input.inj inputs⟩

/-- A positive operation cycle cannot lie on a path from an input.
Otherwise reverse traversal could repeat the cycle before reaching its normal
form, contradicting the deterministic prefix/terminal uniqueness theorem. -/
theorem no_operation_cycle_on_input_path (unary : G.UnaryOperations operation)
    {v : G.Vertex} {es : List G.Edge} {i : Fin I.length}
    (root : G.OperationPath operation (.input i) es v)
    {cycle : List G.Edge} (loop : G.OperationTrace operation v cycle v) : cycle = [] := by
  have det := G.reverseOperations_deterministic operation unary
  have run := root.steps
  have cycleRun := loop.steps
  have full := cycleRun.append run
  have eq := full.final_unique det run (by trivial) (by trivial)
  have zero : cycle.length = 0 := by
    have count := eq.1
    omega
  exact List.length_eq_zero_iff.mp zero

end Hypernets.Graph.Net
