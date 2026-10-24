import Hypernets.Graph.SearchContexts

/-! Explicit simple-hole contexts for the paper's finite search interactions. -/
namespace Hypernets.Linear
open Graph PatternPlugging SearchContexts
variable {Op : Type} {ops : Operations Op} {d : Nat}
namespace PatternPlugging
variable (C : Hypernet ops d [.term] []) (e : C.Edge) (name : Nat)

/-- The same finite fragment, with its interface identified with the explicit hole signature. -/
noncomputable def holeFragment (p : Position C e) :=
  (fragment C e p).reboundary
    (input_eq C e (primitiveLabel ops d (.hole (SearchContexts.hole C e name)))
      (by cases d <;> rfl) (by cases d <;> rfl))
    (output_eq C e (primitiveLabel ops d (.hole (SearchContexts.hole C e name)))
      (by cases d <;> rfl) (by cases d <;> rfl))

/-- Matching an actual state by plugging into the explicit labelled simple context. -/
def HoleMatches (p : Position C e) (s : State ops d) : Prop :=
  Nonempty (Net.Iso ((openSlot C e name).plug e (holeFragment C e name p)) s.graph)

/-- Slot presentation and actual labelled-hole plugging have identical endpoints. -/
theorem holeMatches_iff (p : Position C e) (s : State ops d) :
    HoleMatches C e name p s ↔ Matches C e p s := by
  let a := plug_iso C e (primitiveLabel ops d (.hole (SearchContexts.hole C e name)))
    (by cases d <;> rfl) (by cases d <;> rfl) (fragment C e p)
  constructor
  · rintro ⟨b⟩; exact ⟨a.trans b⟩
  · rintro ⟨b⟩; exact ⟨a.symm.trans b⟩
end PatternPlugging
namespace State

/-- Search by a finite two-edge interaction in one explicit focus-free simple
hole context. The two endpoints use the same context and the same hole. -/
def HoleContextSearch (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  ∃ (C : Hypernet ops d [.term] []), FocusFree C ∧ HoleFree C ∧
    ∃ (e : C.Edge) (name : Nat) (p q : Position C e),
      SearchStep (corolla C e) kind p.val q.val ∧
      HoleMatches C e name p s ∧ HoleMatches C e name q t

/-- The slot and explicit-hole presentations coincide, with no endpoint restrictions added. -/
theorem contextual_iff_holeContext {kind : Op → OperationKind} {s t : State ops d} :
    ContextualSearch kind s t ↔ HoleContextSearch kind s t := by
  constructor
  · rintro ⟨C,free,closed,e,p,q,rule,left,right⟩
    exact ⟨C,free,closed,e,0,p,q,rule,(holeMatches_iff C e 0 p s).mpr left,
      (holeMatches_iff C e 0 q t).mpr right⟩
  · rintro ⟨C,free,closed,e,name,p,q,rule,left,right⟩
    exact ⟨C,free,closed,e,p,q,rule,(holeMatches_iff C e name p s).mp left,
      (holeMatches_iff C e name q t).mp right⟩

/-- Erasure-based state search is exactly explicit simple-context application
of finite search interaction patterns, in both directions. -/
theorem search_iff_holeContext {kind : Op → OperationKind} {s t : State ops d} :
    Search kind s t ↔ HoleContextSearch kind s t :=
  search_iff_contextual.trans contextual_iff_holeContext

/-- The independent incidence equations and explicit-hole pattern rewriting agree. -/
theorem incidenceSearch_iff_holeContext {kind : Op → OperationKind} {s t : State ops d} :
    IncidenceSearch kind s t ↔ HoleContextSearch kind s t :=
  search_iff_incidence.symm.trans search_iff_holeContext

/-- The recursive search relation has the same simple-context interactions. -/
theorem deepSearch_iff_holeContext {kind : Op → OperationKind} {s t : State ops d} :
    DeepSearch kind s t ↔ ∃ u, HoleContextSearch kind s u ∧ Nonempty (Focussed.DeepIso u.focussed t.focussed) := by
  rw [deepSearch_iff]
  simp only [search_iff_holeContext]

/-- No arbitrary simple context is excluded by the closed-slot representation:
a compatible interaction label closes it, and every rule plugged in that original
context yields a state search step. Interface transports only reindex equal boundaries. -/
theorem arbitrary_simple_context
    (C : Hypernet ops d [.term] []) (e : C.Edge) (simple : SearchContexts.Simple C e)
    (l : (alphabet ops d).Symbol)
    (hi : (alphabet ops d).signature.input l = (alphabet ops d).signature.input (C.edgeLabel e))
    (ho : (alphabet ops d).signature.output l = (alphabet ops d).signature.output (C.edgeLabel e))
    (p q : Position (relabel C e l hi ho) e) (kind : Op → OperationKind)
    (rule : SearchStep (corolla (relabel C e l hi ho) e) kind p.val q.val)
    (s t : State ops d)
    (left : Nonempty (Net.Iso
      (C.plug e ((fragment (relabel C e l hi ho) e p).reboundary
        (input_eq C e l hi ho).symm (output_eq C e l hi ho).symm)) s.graph))
    (right : Nonempty (Net.Iso
      (C.plug e ((fragment (relabel C e l hi ho) e q).reboundary
        (input_eq C e l hi ho).symm (output_eq C e l hi ho).symm)) t.graph)) :
    Search kind s t := by
  have conditions := interaction_closed (relabel C e l hi ho) e rule
  rw [selected_label] at conditions
  obtain ⟨free,closed⟩ := close_simple C e simple l hi ho conditions.1 conditions.2
  obtain ⟨a⟩ := left
  obtain ⟨b⟩ := right
  apply contextualSearch_sound
  exact ⟨relabel C e l hi ho,free,closed,e,p,q,rule,
    ⟨(plug_iso_reverse C e l hi ho _).trans a⟩,
    ⟨(plug_iso_reverse C e l hi ho _).trans b⟩⟩
end State
end Hypernets.Linear
