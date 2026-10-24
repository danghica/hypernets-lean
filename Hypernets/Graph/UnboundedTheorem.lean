import Hypernets.Graph.UnboundedObservations
import Hypernets.Graph.PaperRelations

/-! The two sufficiency clauses for depth-independent pre-templates and observations. -/
namespace Hypernets.Linear.Unbounded
open ObservationFillings ConcreteObservations
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- Contextual refinement of depth-independent graphs: test every finite representative,
every hole name and every independently specified finite observation context. Execution
uses the unbounded machine; the representation depth does not bound the run. -/
def PaperRefines (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop) (B : Behaviour ops kind)
    (Q : CostOrder) {I O} (G H : PaperEncoding.GlobalClass ops I O) : Prop :=
  ∀ name n (g h : Hypernet ops n I O), PaperEncoding.interpret ops g = G →
    PaperEncoding.interpret ops h = H →
    (Unbounded.observations Allowed).Refines (machine B) Q
      (singleFragment ⟨name,I,O⟩ g) (singleFragment ⟨name,I,O⟩ h)

/-- Any graph representative can be moved to any larger finite allowance. -/
theorem representative_at {n m I O} (le : n ≤ m) (G : Hypernet ops n I O) :
    ∃ H : Hypernet ops m I O, PaperEncoding.interpret ops H = PaperEncoding.interpret ops G := by
  obtain ⟨k,rfl⟩ := Nat.le.dest le
  clear le
  induction k with
  | zero => exact ⟨G,rfl⟩
  | succ k ih =>
    obtain ⟨H,h⟩ := ih
    exact ⟨Linear.raise ops (n+k) H,(PaperEncoding.interpret_raise ops H).symm.trans h⟩

/-- The universal representative formulation is non-vacuous: every pair of global
fragment classes has representatives at a common depth, and at every larger depth. -/
theorem common_representatives {I O} (G H : PaperEncoding.GlobalClass ops I O) :
    ∃ bound, ∀ m, bound ≤ m → ∃ g h : Hypernet ops m I O,
      PaperEncoding.interpret ops g = G ∧ PaperEncoding.interpret ops h = H := by
  obtain ⟨n,g,hg⟩ := PaperEncoding.interpret_surjective ops G
  obtain ⟨k,h,hh⟩ := PaperEncoding.interpret_surjective ops H
  refine ⟨n+k,fun m hm => ?_⟩
  obtain ⟨g',hg'⟩ := representative_at (by omega : n ≤ m) g
  obtain ⟨h',hh'⟩ := representative_at (by omega : k ≤ m) h
  exact ⟨g',h',hg'.trans hg,hh'.trans hh⟩

variable (T : PaperEncoding.GlobalPreTemplate ops)
    (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop) (B : Behaviour ops kind)
    (allowed : ∀ n, IsoClosedContexts (Allowed n))
    (closed : ∀ n, (T.toLayered ops n).OutputClosed) (refocusing : B.Refocusing)

include allowed closed refocusing in
/-- Theorem 6(1), evaluated on the union of finite depths and a global pre-template. -/
theorem paper_sufficiency {Q P R : CostOrder} (det : B.Deterministic) (reasonable : Reasonable Q P R)
    (safe : Safety.InputSafe (T.toLayered ops) Allowed B Q P)
    (robust : Safety.Robust (T.toLayered ops) Allowed B Q P R)
    {I O} {G H : PaperEncoding.GlobalClass ops I O} (rel : T.Rel G H) :
    PaperRefines Allowed B Q G H := by
  intro name n g h hg hh
  have related : (T.toLayered ops n).Rel g h := by
    change T.Rel (PaperEncoding.interpret ops g) (PaperEncoding.interpret ops h)
    rw [hg,hh]
    exact rel
  exact Unbounded.sufficiency (T.toLayered ops) Allowed B allowed closed refocusing det reasonable safe robust
    ((single_related_iff (T.toLayered ops) ⟨name,I,O⟩ g h).mpr related)

include allowed closed refocusing in
/-- Theorem 6(2), with converse costs for input safety and converse robustness. -/
theorem paper_sufficiency_converse {Q P R : CostOrder} (det : B.Deterministic)
    (reasonable : Reasonable Q P R)
    (safe : Safety.InputSafe (T.toLayered ops) Allowed B Q.converse P)
    (robust : Safety.ConverseRobust (T.toLayered ops) Allowed B Q P R)
    {I O} {G H : PaperEncoding.GlobalClass ops I O} (rel : T.Rel G H) :
    PaperRefines Allowed B Q H G := by
  intro name n h g hh hg
  have related : (T.toLayered ops n).Rel g h := by
    change T.Rel (PaperEncoding.interpret ops g) (PaperEncoding.interpret ops h)
    rw [hg,hh]
    exact rel
  exact Unbounded.sufficiency_converse (T.toLayered ops) Allowed B allowed closed refocusing det reasonable safe robust
    ((single_related_iff (T.toLayered ops) ⟨name,I,O⟩ g h).mpr related)

include allowed closed refocusing in
/-- Both unbounded contextual refinements follow from the two concrete sets of hypotheses. -/
theorem paper_equivalence {Q P R : CostOrder} (det : B.Deterministic) (reasonable : Reasonable Q P R)
    (safe : Safety.InputSafe (T.toLayered ops) Allowed B Q P)
    (safeConverse : Safety.InputSafe (T.toLayered ops) Allowed B Q.converse P)
    (robust : Safety.Robust (T.toLayered ops) Allowed B Q P R)
    (robustConverse : Safety.ConverseRobust (T.toLayered ops) Allowed B Q P R)
    {I O} {G H : PaperEncoding.GlobalClass ops I O} (rel : T.Rel G H) :
    PaperRefines Allowed B Q G H ∧ PaperRefines Allowed B Q H G :=
  ⟨paper_sufficiency T Allowed B allowed closed refocusing det reasonable safe robust rel,
    paper_sufficiency_converse T Allowed B allowed closed refocusing det reasonable safeConverse robustConverse rel⟩
/-- A set of depth-independent contexts determines membership at every finite presentation. -/
noncomputable def globalAllowed (C : PaperEncoding.GlobalClass ops [.term] [] → Prop)
    (n : Nat) (G : Hypernet ops n [.term] []) : Prop := C (PaperEncoding.interpret ops G)

/-- Global context membership is automatically independent of graph names. -/
theorem globalAllowed_iso (C : PaperEncoding.GlobalClass ops [.term] [] → Prop) (n : Nat) :
    IsoClosedContexts (globalAllowed C n) := by
  intro G H f h
  change C (PaperEncoding.interpret ops H)
  rw [← PaperEncoding.interpret_iso ops (DeepIso.ofIso f)]
  exact h

/-- Global context membership is also independent of unused depth allowance. -/
theorem globalAllowed_padding (C : PaperEncoding.GlobalClass ops [.term] [] → Prop)
    {n} (G : Hypernet ops n [.term] []) : globalAllowed C (n+1) (DepthPadding.graph G) ↔ globalAllowed C n G := by
  unfold globalAllowed
  rw [DepthPadding.graph_eq_raise,← PaperEncoding.interpret_raise]

/-- Theorem 6's two implications for one global context set and one global pre-template.
The original safety, output-closure and robustness hypotheses remain hypotheses;
all machine, locality, observation and depth-transfer obligations have been proved. -/
theorem theorem6 (C : PaperEncoding.GlobalClass ops [.term] [] → Prop)
    (T : PaperEncoding.GlobalPreTemplate ops) (B : Behaviour ops kind)
    (closed : ∀ n, (T.toLayered ops n).OutputClosed) (refocusing : B.Refocusing)
    (det : B.Deterministic) {Q P R : CostOrder} (reasonable : Reasonable Q P R) :
    (Safety.InputSafe (T.toLayered ops) (globalAllowed C) B Q P →
      Safety.Robust (T.toLayered ops) (globalAllowed C) B Q P R →
      ∀ {I O} {G H : PaperEncoding.GlobalClass ops I O}, T.Rel G H → PaperRefines (globalAllowed C) B Q G H) ∧
    (Safety.InputSafe (T.toLayered ops) (globalAllowed C) B Q.converse P →
      Safety.ConverseRobust (T.toLayered ops) (globalAllowed C) B Q P R →
      ∀ {I O} {G H : PaperEncoding.GlobalClass ops I O}, T.Rel G H → PaperRefines (globalAllowed C) B Q H G) := by
  constructor
  · intro safe robust I O G H rel
    exact paper_sufficiency T (globalAllowed C) B (globalAllowed_iso C) closed refocusing det reasonable safe robust rel
  · intro safe robust I O G H rel
    exact paper_sufficiency_converse T (globalAllowed C) B (globalAllowed_iso C) closed refocusing det reasonable safe robust rel
end Hypernets.Linear.Unbounded
